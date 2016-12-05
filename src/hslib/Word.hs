{-# OPTIONS_GHC -XMagicHash #-}

module Word where

import Data.Bits
import Data.Word
import GHC.Prim
import GHC.Types
import GHC.Integer.GMP.Internals

data Coq_word =
    W Integer
  | W64 !Word64

-- Memoize bitmasks for wrap
bitmask :: [Integer]
bitmask = map (\x -> 2^x - 1) [(0::Int) ..]

wrap :: Integer -> Integer -> Coq_word
wrap 64 v = W64 $ fromIntegral v
wrap nbits v = W $ (Data.Bits..&.) v (bitmask !! (fromIntegral nbits))

weq :: Integer -> Coq_word -> Coq_word -> Bool
weq _ (W x) (W y) = x == y
weq _ (W x) (W64 y) = (fromIntegral x) == y
weq _ (W64 x) (W y) = x == (fromIntegral y)
weq _ (W64 x) (W64 y) = x == y

wlt_dec :: Integer -> Coq_word -> Coq_word -> Bool
wlt_dec _ (W x) (W y) = x < y
wlt_dec _ (W x) (W64 y) = (fromIntegral x) < y
wlt_dec _ (W64 x) (W y) = x < (fromIntegral y)
wlt_dec _ (W64 x) (W64 y) = x < y

bit_dec :: Coq_word -> Bool
bit_dec (W 0) = True
bit_dec (W64 0) = True
bit_dec _ = False

wplus :: Integer -> Coq_word -> Coq_word -> Coq_word
wplus n (W x) (W y) = wrap n (x + y)
wplus _ (W x) (W64 y) = W64 $ (fromIntegral x) + y
wplus _ (W64 x) (W y) = W64 $ x + (fromIntegral y)
wplus _ (W64 x) (W64 y) = W64 $ x + y

wminus :: Integer -> Coq_word -> Coq_word -> Coq_word
wminus n (W x) (W y) = wrap n (2^n + x - y)
wminus _ (W x) (W64 y) = W64 $ (fromIntegral x) - y
wminus _ (W64 x) (W y) = W64 $ x - (fromIntegral y)
wminus _ (W64 x) (W64 y) = W64 $ x - y

wmult :: Integer -> Coq_word -> Coq_word -> Coq_word
wmult n (W x) (W y) = wrap n (x * y)
wmult _ (W x) (W64 y) = W64 $ (fromIntegral x) * y
wmult _ (W64 x) (W y) = W64 $ x * (fromIntegral y)
wmult _ (W64 x) (W64 y) = W64 $ (x * y)

wdiv :: Integer -> Coq_word -> Coq_word -> Coq_word
wdiv _ (W x) (W y) = W $ x `quot` y
wdiv _ (W x) (W64 y) = W64 $ (fromIntegral x) `quot` y
wdiv _ (W64 x) (W y) = W64 $ x `quot` (fromIntegral y)
wdiv _ (W64 x) (W64 y) = W64 $ x `quot` y

wmod :: Integer -> Coq_word -> Coq_word -> Coq_word
wmod _ (W x) (W y) = W $ x `rem` y
wmod _ (W x) (W64 y) = W64 $ (fromIntegral x) `rem` y
wmod _ (W64 x) (W y) = W64 $ x `rem` (fromIntegral y)
wmod _ (W64 x) (W64 y) = W64 $ x `rem` y

wbit :: Integer -> Integer -> Coq_word -> Coq_word
wbit sz _ (W n) = wrap sz (2^n)
wbit sz _ (W64 n) = wrap sz (2^n)

wand :: Integer -> Coq_word -> Coq_word -> Coq_word
wand _ (W x) (W y) = W $ (Data.Bits..&.) x y
wand _ (W x) (W64 y) = W64 $ (Data.Bits..&.) (fromIntegral x) y
wand _ (W64 x) (W y) = W64 $ (Data.Bits..&.) x (fromIntegral y)
wand _ (W64 x) (W64 y) = W64 $ (Data.Bits..&.) x y

wor :: Integer -> Coq_word -> Coq_word -> Coq_word
wor _ (W x) (W y) = W $ (Data.Bits..|.) x y
wor _ (W x) (W64 y) = W64 $ (Data.Bits..|.) (fromIntegral x) y
wor _ (W64 x) (W y) = W64 $ (Data.Bits..|.) x (fromIntegral y)
wor _ (W64 x) (W64 y) = W64 $ (Data.Bits..|.) x y

natToWord :: Integer -> Integer -> Coq_word
natToWord _ 0 = W 0
natToWord n x = wrap n $ fromIntegral x

wordToNat :: Integer -> Coq_word -> Integer
wordToNat _ (W x) = fromIntegral x
wordToNat _ (W64 x) = fromIntegral x

wzero :: Integer -> Coq_word
wzero 64 = W64 0
wzero _ = W 0

zext :: Integer -> Coq_word -> Integer -> Coq_word
zext _ (W w) _ = W w
zext _ (W64 w) _ = W $ fromIntegral w

split1 :: Integer -> Integer -> Coq_word -> Coq_word
split1 _ _ (W (S# 0#)) = W $ S# 0#
split1 sz1 _ (W (Jp# (BN# ba)))
  | (fromIntegral sz1) >= 8 * I# (sizeofByteArray# ba) = W $ Jp# $ BN# ba
  | sz1 `rem` 8 == 0 = case (fromIntegral sz1) `quot` 8 of
    (I# sz1#) -> W $ importIntegerFromByteArray ba 0## (int2Word# sz1#) 0#
split1 sz1 _ (W (S# i))
  | sz1 >= 64 = W $ S# i
split1 sz1 _ (W w) = wrap sz1 w
split1 sz1 sz2 (W64 w) = split1 sz1 sz2 (W $ fromIntegral w)

split2 :: Integer -> Integer -> Coq_word -> Coq_word
-- split2 sz1 sz2 (W (Jp# (BN# ba)))
--   | sz1 >= 8 * I# (sizeofByteArray# ba) = W 0
--   | sz1 `rem` 8 == 0 && sz2 `rem` 8 == 0 = case sz1 `quot` 8 of
--     (I# sz1#) -> case sz2 `quot` 8 of
--       (I# sz2#) -> W $ importIntegerFromByteArray ba (int2Word# sz1#) (int2Word# sz2#) 0#
split2 sz1 _ (W w) = W $ w `Data.Bits.shiftR` (fromIntegral sz1)
split2 sz1 sz2 (W64 w) = split2 sz1 sz2 (W $ fromIntegral w)

combine :: Integer -> Coq_word -> Integer -> Coq_word -> Coq_word
combine sz1 (W w1) _ (W w2) = W $ w1 + (w2 `Data.Bits.shiftL` (fromIntegral sz1))
combine sz1 (W w1) sz2 (W64 w2) = combine sz1 (W w1) sz2 (W $ fromIntegral w2)
combine sz1 (W64 w1) sz2 (W w2) = combine sz1 (W $ fromIntegral w1) sz2 (W w2)
combine sz1 (W64 w1) sz2 (W64 w2) = combine sz1 (W $ fromIntegral w1) sz2 (W $ fromIntegral w2)

maxShift :: Integer
maxShift = fromIntegral (maxBound :: Int)

wlshift :: Integer ->  Coq_word -> Integer -> Coq_word
wlshift sz w1 s -- handle shifts larger than maxShift recursively
    | s > maxShift = wlshift sz (wlshift sz w1 maxShift) (s - maxShift)
wlshift _  (W w1) s = W $ w1 `Data.Bits.shiftL` (fromIntegral s)
wlshift _ (W64 w1) w2 = W64 $ w1 `Data.Bits.shiftL` (fromIntegral w2)

wrshift :: Integer ->  Coq_word -> Integer -> Coq_word
wrshift sz w1 s -- handle shifts larger than maxShift recursively
    | s > maxShift = wrshift sz (wrshift sz w1 maxShift) (s - maxShift)
wrshift _  (W w1) s = W $ w1 `Data.Bits.shiftR` (fromIntegral s)
wrshift _ (W64 w1) w2 = W64 $ w1 `Data.Bits.shiftR` (fromIntegral w2)

wnot :: Integer -> Coq_word -> Coq_word
wnot _ (W w) = W $ complement w
wnot _ (W64 w) = W64 $ complement w

wones :: Integer -> Coq_word
wones n  = W $ (bitmask !! (fromIntegral n))


-- Why is this in Word.v to begin with?
pow2 :: Integer -> Integer
pow2 i = 2^i

instance Show Coq_word where
  show (W x) = show x
  show (W64 x) = show x

instance Eq Coq_word where
  a == b = weq 0 a b

instance Ord Coq_word where
  a <= b = (wlt_dec 0 a b) || (weq 0 a b)
