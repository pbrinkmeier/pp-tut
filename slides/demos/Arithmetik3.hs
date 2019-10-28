module Arithmetik3 where

pow3 base exp = pow3Acc base exp 1
  where
    pow3Acc base exp acc
      | exp == 0         = acc
      | exp `mod` 2 == 0 = pow3Acc (base * base) (exp `div` 2) acc
      | otherwise        = pow3Acc base (exp - 1) (base * acc)
