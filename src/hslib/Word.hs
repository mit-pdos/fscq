module Word where

import Data.Bits

data Coq_word = W !Integer

wrap :: Integer -> Integer -> Integer
wrap nbits v = (Data.Bits..&.) v (2^nbits - 1)

weq :: Integer -> Coq_word -> Coq_word -> Bool
weq _ (W x) (W y) = x == y

wlt_dec :: Integer -> Coq_word -> Coq_word -> Bool
wlt_dec _ (W x) (W y) = x < y

wplus :: Integer -> Coq_word -> Coq_word -> Coq_word
wplus n (W x) (W y) = W $ wrap n (x + y)

wminus :: Integer -> Coq_word -> Coq_word -> Coq_word
wminus n (W x) (W y) = W $ wrap n (2^n + x - y)

wmult :: Integer -> Coq_word -> Coq_word -> Coq_word
wmult n (W x) (W y) = W $ wrap n (x * y)

wdiv :: Integer -> Coq_word -> Coq_word -> Coq_word
wdiv _ (W x) (W y) = W $ x `quot` y

wmod :: Integer -> Coq_word -> Coq_word -> Coq_word
wmod _ (W x) (W y) = W $ x `rem` y

natToWord :: Integer -> Integer -> Coq_word
natToWord n x = W $ wrap n $ fromIntegral x

wordToNat :: Integer -> Coq_word -> Integer
wordToNat _ (W x) = x

zext :: Integer -> Coq_word -> Integer -> Coq_word
zext _ (W w) _ = W w

split1 :: Integer -> Integer -> Coq_word -> Coq_word
split1 sz1 _ (W w) = W $ wrap sz1 w

split2 :: Integer -> Integer -> Coq_word -> Coq_word
split2 sz1 _ (W w) = W $ w `Data.Bits.shiftR` (fromIntegral sz1)

combine :: Integer -> Coq_word -> Integer -> Coq_word -> Coq_word
combine sz1 (W w1) _ (W w2) = W $ w1 + (w2 `Data.Bits.shiftL` (fromIntegral sz1))

instance Show Coq_word where
  show (W x) = show x
