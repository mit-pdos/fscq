module Word where

import qualified Data.Word
import qualified Data.ByteString
import qualified Data.Serialize as S -- cabal install cereal

data Coq_word =
   W64 !Data.Word.Word64
 | W4096 Data.ByteString.ByteString

weq :: Prelude.Integer -> Coq_word -> Coq_word -> Prelude.Bool
weq _ (W64 x) (W64 y) = x == y
weq _ (W4096 x) (W4096 y) = x == y
weq _ _ _ = False

wlt_dec :: Prelude.Integer -> Coq_word -> Coq_word -> Prelude.Bool
wlt_dec _ (W64 x) (W64 y) = x < y
wlt_dec _ _ _ = error "wlt_dec W4096"

wplus :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wplus _ (W64 x) (W64 y) = W64 (x + y)
wplus _ _ _ = error "wplus W4096"

wminus :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wminus _ (W64 x) (W64 y) = W64 (x - y)
wminus _ _ _ = error "wminus W4096"

wmult :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wmult _ (W64 x) (W64 y) = W64 (x * y)
wmult _ _ _ = error "wmult W4096"

natToWord :: Prelude.Integer -> Prelude.Integer -> Coq_word
natToWord 64 x = W64 (fromIntegral x)
natToWord 4096 0 = W4096 $ Data.ByteString.replicate 512 0
natToWord 4096 1 = W4096 $ Data.ByteString.append (Data.ByteString.replicate 511 0)
                                                  (Data.ByteString.replicate 1 1)
natToWord 4096 x = error $ "natToWord unexpected W4096 value: " ++ show x
natToWord sz _ = error $ "natToWord unexpected size: " ++ show sz

zext :: Prelude.Integer -> Coq_word -> Prelude.Integer -> Coq_word
zext _ (W64 w) sz' | sz' == 4096-64 = W4096 x
  where
    x = S.runPut (S.putByteString zeros >> S.putWord64be w)
    zeros = Data.ByteString.replicate (512-8) 0
zext _ (W64 _) _ = error "zext not 4096-64"
zext _ _ _ = error "zext W4096"

split1 :: Prelude.Integer -> Prelude.Integer -> Coq_word -> Coq_word
split1 64 _ (W4096 w) = W64 x
  where
    get = S.uncheckedSkip (512-8) >> S.getWord64be
    x = case S.runGet get w of
        Left err -> error $ "split1: " ++ err
        Right z -> z
split1 _ _ (W4096 _) = error "split1 not 64"
split1 _ _ (W64 _) = error "split1 W64"

instance Show Coq_word where
  show (W64 x) = show x
  show (W4096 x) = "[[W4096]]"
