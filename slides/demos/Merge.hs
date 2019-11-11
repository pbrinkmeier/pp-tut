module Merge where

import Sort (merge)
import Primes (primes)

primepowers n = mergeAll $ map primesexp [1..n]
  where mergeAll = foldl merge []
        primesexp i = map (^i) primes
