module Merge where

import Primes (primes)

merge (x:xs) (y:ys)
  | x <= y    = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys
merge xs ys = xs ++ ys

primepowers n = mergeAll $ map primesExp [1..n]
  where mergeAll = foldl merge []
        primesExp i = map (^i) primes
