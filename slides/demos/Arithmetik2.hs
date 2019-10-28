module Arithmetik2 where

pow2 base exp
  | exp == 0         = 1
  | exp `mod` 2 == 0 = pow2 (base * base) (exp `div` 2)
  | otherwise        = base * (pow2 base (exp - 1))
