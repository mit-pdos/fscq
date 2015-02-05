module Word where

import Data.Bits

data Coq_word = W !Integer

-- Memoize bitmasks for wrap
bitmask :: [Integer]
bitmask = map (\x -> 2^x - 1) [(0::Int) ..]

wrap :: Int -> Integer -> Integer
wrap nbits v = (Data.Bits..&.) v (bitmask !! nbits)

weq :: Int -> Coq_word -> Coq_word -> Bool
weq _ (W x) (W y) = x == y

wlt_dec :: Int -> Coq_word -> Coq_word -> Bool
wlt_dec _ (W x) (W y) = x < y

wplus :: Int -> Coq_word -> Coq_word -> Coq_word
wplus n (W x) (W y) = W $ wrap n (x + y)

wminus :: Int -> Coq_word -> Coq_word -> Coq_word
wminus n (W x) (W y) = W $ wrap n (2^n + x - y)

wmult :: Int -> Coq_word -> Coq_word -> Coq_word
wmult n (W x) (W y) = W $ wrap n (x * y)

wdiv :: Int -> Coq_word -> Coq_word -> Coq_word
wdiv _ (W x) (W y) = W $ x `quot` y

wmod :: Int -> Coq_word -> Coq_word -> Coq_word
wmod _ (W x) (W y) = W $ x `rem` y

natToWord :: Int -> Int -> Coq_word
natToWord _ 0 = W 0
natToWord n x = W $ wrap n $ fromIntegral x

wordToNat :: Int -> Coq_word -> Int
wordToNat _ (W x) = fromIntegral x

zext :: Int -> Coq_word -> Int -> Coq_word
zext _ (W w) _ = W w

split1 :: Int -> Int -> Coq_word -> Coq_word
split1 sz1 _ (W w) = W $ wrap sz1 w

split2 :: Int -> Int -> Coq_word -> Coq_word
split2 sz1 _ (W w) = W $ w `Data.Bits.shiftR` (fromIntegral sz1)

combine :: Int -> Coq_word -> Int -> Coq_word -> Coq_word
combine sz1 (W w1) _ (W w2) = W $ w1 + (w2 `Data.Bits.shiftL` (fromIntegral sz1))

instance Show Coq_word where
  show (W x) = show x
