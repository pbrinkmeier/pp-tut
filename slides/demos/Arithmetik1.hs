module Arithmetik1 where

pow1 base exp
  | exp == 0  = 1
  | otherwise = base * (pow1 base (exp - 1))
