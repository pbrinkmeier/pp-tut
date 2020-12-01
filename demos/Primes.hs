module Primes where

primes :: [Integer]
primes = sieve [2..]
  where sieve []         = []
        sieve (p : rest) = p : sieve [x | x <- rest, x `mod` p /= 0]
