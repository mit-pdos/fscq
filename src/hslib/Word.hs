module Word where

import qualified Data.Word
import qualified Data.ByteString
import qualified Data.Serialize as S -- cabal install cereal // apt-get install libghc-cereal-dev
import qualified Data.Bits

data Coq_word =
   WO
 | W64 !Data.Word.Word64
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
split1 _ _ WO = error "split1 WO"

split2 :: Prelude.Integer -> Prelude.Integer -> Coq_word -> Coq_word
split2 _ _ _ = error "split2 not implemented"

combine :: Prelude.Integer -> Coq_word -> Prelude.Integer -> Coq_word -> Coq_word
combine _ _ _ _ = error "combine not implemented"

wbit :: Prelude.Integer -> Prelude.Integer -> Coq_word -> Coq_word
wbit 4096 64 (W64 n) = W4096 $ Data.ByteString.append prefix
                             $ Data.ByteString.append byte suffix
  where
    ni = fromIntegral n
    prefix = Data.ByteString.replicate (511 - (ni `div` 8)) 0
    byte = Data.ByteString.replicate 1 (Data.Bits.shift 1 (ni `mod` 8))
    suffix = Data.ByteString.replicate (ni `div` 8) 0
wbit _ _ _ = error "wbit not 4096/64"

wand :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wand 4096 (W4096 a) (W4096 b) = W4096 c
  where
    c = Data.ByteString.pack $ Data.ByteString.zipWith (Data.Bits..&.) a b
wand _ _ _ = error "wand not 4096"

wor :: Prelude.Integer -> Coq_word -> Coq_word -> Coq_word
wor 4096 (W4096 a) (W4096 b) = W4096 c
  where
    c = Data.ByteString.pack $ Data.ByteString.zipWith (Data.Bits..|.) a b
wor _ _ _ = error "wand not 4096"

wnot :: Prelude.Integer -> Coq_word -> Coq_word
wnot 4096 (W4096 a) = W4096 b
  where
    b = Data.ByteString.map (\x -> Data.Bits.xor x 0xff) a
wnot _ _ = error "wnot not 4096"

instance Show Coq_word where
  show WO = "[[WO]]"
  show (W64 x) = show x
  show (W4096 _) = "[[W4096]]"
