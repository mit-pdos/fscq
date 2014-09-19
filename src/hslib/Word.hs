module Word where

import qualified Data.Word
import qualified Data.ByteString
import qualified Data.Bits

data Coq_word =
   W64 Data.Word.Word64
 | W4096 Data.ByteString.ByteString

weq :: Prelude.Integer -> Coq_word -> Coq_word -> Prelude.Bool
weq sz x y = case x of {
  W64 x' -> case y of { W64 y' -> x' == y'; _ -> False };
  W4096 x' -> case y of { W4096 y' -> x' == y'; _ -> False }
}

wlt_dec :: Prelude.Integer -> Coq_word -> Coq_word -> Prelude.Bool
wlt_dec sz x y = case x of {
  W64 x' -> case y of { W64 y' -> (x' < y'); _ -> error "wlt_dec W4096y" };
  W4096 x' -> error "wlt_dec W4096x"
}

wplus :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wplus sz x y = case x of {
  W64 x' -> case y of {
    W64 y' -> W64 (x' + y');
    _ -> error "wplus W4096y"
  };
  _ -> error "wplus W4096x"
}

wminus :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wminus sz x y = case x of {
  W64 x' -> case y of {
    W64 y' -> W64 (x' - y');
    _ -> error "wminus W4096y"
  };
  _ -> error "wminus W4096x"
}

wmult :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wmult sz x y = case x of {
  W64 x' -> case y of {
    W64 y' -> W64 (x' * y');
    _ -> error "wmult W4096y"
  };
  _ -> error "wmult W4096x"
}

natToWord :: Prelude.Integer -> Prelude.Integer -> Coq_word
natToWord sz x = case sz of {
  64 -> W64 $ fromIntegral x;
  4096 -> case x of {
    0 -> W4096 $ Data.ByteString.replicate 512 0;
    1 -> W4096 $ Data.ByteString.append
                 (Data.ByteString.replicate 511 0)
                 (Data.ByteString.replicate 1 1);
    _ -> error "natToWord unexpected W4096 value"
  };
  _ -> error "natToWord unexpected size"
}

unpack64 :: Data.Word.Word64 -> [Data.Word.Word8]
unpack64 x = map (fromIntegral.(Data.Bits.shiftR x)) [56,48..0]

pack64 :: [Data.Word.Word8] -> Data.Word.Word64
pack64 x = foldl (\a x -> a Data.Bits..|. x) 0 $
           zipWith (\x s -> Data.Bits.shiftL ((fromIntegral x) :: Data.Word.Word64) s) x [56,48..0]

zext :: Prelude.Integer -> Coq_word -> Prelude.Integer -> Coq_word
zext sz w sz' = case w of {
  W64 w' ->
    if (sz' == 4096-64) then
      W4096 $ Data.ByteString.append (Data.ByteString.replicate (512-8) 0)
                                     (Data.ByteString.pack $ unpack64 w')
    else
      error "zext not 4096-64";
  _ -> error "zext W4096"
}

split1 :: Prelude.Integer -> Prelude.Integer -> Coq_word -> Coq_word
split1 sz1 sz2 w = case w of {
  W4096 w' ->
    if (sz1 == 64) then
      W64 $ pack64 $ Data.ByteString.unpack $
                     Data.ByteString.drop (512-8) w'
    else
      error "split1 not 64";
  _ -> error "split1 W64"
}

