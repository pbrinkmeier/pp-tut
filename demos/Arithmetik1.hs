module Arithmetik1 where

pow1 b e | e < 0     = error "e negativ"
         | e == 0    = 1
         | otherwise = b * pow1 b (e-1)

pow2 b e
  | e < 0          = error "e negativ"
  | e == 0         = 1
  | e `mod` 2 == 0 =     pow2 (b * b) (e `div` 2)
  | otherwise      = b * pow2 (b * b) (e `div` 2)
