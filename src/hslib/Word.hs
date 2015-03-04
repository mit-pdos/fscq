{-# OPTIONS_GHC -XMagicHash #-}

module Word where

import Data.Bits
import Data.Word
import GHC.Prim
import GHC.Types
import GHC.Integer.GMP.Internals

data Coq_word =
    W !Integer
  | W64 !Word64

-- Memoize bitmasks for wrap
bitmask :: [Integer]
bitmask = map (\x -> 2^x - 1) [(0::Int) ..]

wrap :: Int -> Integer -> Coq_word
wrap 64 v = W64 $ fromIntegral v
wrap nbits v = W $ (Data.Bits..&.) v (bitmask !! nbits)

weq :: Int -> Coq_word -> Coq_word -> Bool
weq _ (W x) (W y) = x == y
weq _ (W x) (W64 y) = (fromIntegral x) == y
weq _ (W64 x) (W y) = x == (fromIntegral y)
weq _ (W64 x) (W64 y) = x == y

wlt_dec :: Int -> Coq_word -> Coq_word -> Bool
wlt_dec _ (W x) (W y) = x < y
wlt_dec _ (W x) (W64 y) = (fromIntegral x) < y
wlt_dec _ (W64 x) (W y) = x < (fromIntegral y)
wlt_dec _ (W64 x) (W64 y) = x < y

wplus :: Int -> Coq_word -> Coq_word -> Coq_word
wplus n (W x) (W y) = wrap n (x + y)
wplus _ (W x) (W64 y) = W64 $ (fromIntegral x) + y
wplus _ (W64 x) (W y) = W64 $ x + (fromIntegral y)
wplus _ (W64 x) (W64 y) = W64 $ x + y

wminus :: Int -> Coq_word -> Coq_word -> Coq_word
wminus n (W x) (W y) = wrap n (2^n + x - y)
wminus _ (W x) (W64 y) = W64 $ (fromIntegral x) - y
wminus _ (W64 x) (W y) = W64 $ x - (fromIntegral y)
wminus _ (W64 x) (W64 y) = W64 $ x - y

wmult :: Int -> Coq_word -> Coq_word -> Coq_word
wmult n (W x) (W y) = wrap n (x * y)
wmult _ (W x) (W64 y) = W64 $ (fromIntegral x) * y
wmult _ (W64 x) (W y) = W64 $ x * (fromIntegral y)
wmult _ (W64 x) (W64 y) = W64 $ (x * y)

wdiv :: Int -> Coq_word -> Coq_word -> Coq_word
wdiv _ (W x) (W y) = W $ x `quot` y
wdiv _ (W x) (W64 y) = W64 $ (fromIntegral x) `quot` y
wdiv _ (W64 x) (W y) = W64 $ x `quot` (fromIntegral y)
wdiv _ (W64 x) (W64 y) = W64 $ x `quot` y

wmod :: Int -> Coq_word -> Coq_word -> Coq_word
wmod _ (W x) (W y) = W $ x `rem` y
wmod _ (W x) (W64 y) = W64 $ (fromIntegral x) `rem` y
wmod _ (W64 x) (W y) = W64 $ x `rem` (fromIntegral y)
wmod _ (W64 x) (W64 y) = W64 $ x `rem` y

wbit :: Int -> Int -> Coq_word -> Coq_word
wbit sz _ (W n) = wrap sz (2^n)
wbit sz _ (W64 n) = wrap sz (2^n)

wand :: Int -> Coq_word -> Coq_word -> Coq_word
wand _ (W x) (W y) = W $ (Data.Bits..&.) x y
wand _ (W x) (W64 y) = W64 $ (Data.Bits..&.) (fromIntegral x) y
wand _ (W64 x) (W y) = W64 $ (Data.Bits..&.) x (fromIntegral y)
wand _ (W64 x) (W64 y) = W64 $ (Data.Bits..&.) x y

natToWord :: Int -> Int -> Coq_word
natToWord _ 0 = W 0
natToWord n x = wrap n $ fromIntegral x

wordToNat :: Int -> Coq_word -> Int
wordToNat _ (W x) = fromIntegral x
wordToNat _ (W64 x) = fromIntegral x

wzero :: Int -> Coq_word
wzero 64 = W64 0
wzero _ = W 0

zext :: Int -> Coq_word -> Int -> Coq_word
zext _ (W w) _ = W w
zext _ (W64 w) _ = W $ fromIntegral w

split1 :: Int -> Int -> Coq_word -> Coq_word
split1 sz1 _ (W (Jp# (BN# ba)))
  | sz1 > 8 * I# (sizeofByteArray# ba) = W $ Jp# $ BN# ba
  | sz1 `rem` 8 == 0 = case sz1 `quot` 8 of
    (I# sz1#) -> W $ importIntegerFromByteArray ba 0## (int2Word# sz1#) 0#
split1 sz1 _ (W w) = wrap sz1 w
split1 sz1 sz2 (W64 w) = split1 sz1 sz2 (W $ fromIntegral w)

split2 :: Int -> Int -> Coq_word -> Coq_word
split2 sz1 _ (W w) = W $ w `Data.Bits.shiftR` (fromIntegral sz1)
split2 sz1 sz2 (W64 w) = split2 sz1 sz2 (W $ fromIntegral w)

combine :: Int -> Coq_word -> Int -> Coq_word -> Coq_word
combine sz1 (W w1) _ (W w2) = W $ w1 + (w2 `Data.Bits.shiftL` (fromIntegral sz1))
combine sz1 (W w1) sz2 (W64 w2) = combine sz1 (W w1) sz2 (W $ fromIntegral w2)
combine sz1 (W64 w1) sz2 (W w2) = combine sz1 (W $ fromIntegral w1) sz2 (W w2)
combine sz1 (W64 w1) sz2 (W64 w2) = combine sz1 (W $ fromIntegral w1) sz2 (W $ fromIntegral w2)

instance Show Coq_word where
  show (W x) = show x
  show (W64 x) = show x
