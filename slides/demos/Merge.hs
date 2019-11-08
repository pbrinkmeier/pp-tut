module Merge where

evens = 0 : map (+ 2) evens
odds  = map (+ 1) evens

merge a [] = a
merge [] b = b
merge (a : as) (b : bs)
  | a <= b     = a : merge as (b : bs)
  | otherwise = b : merge (a : as) bs

primes = 2 : primes' [] (map (+ 2) odds)
  where
    primes' ps (n : ns)
      | not $ any (divides n) ps = n : primes' (n : ps) ns
      | otherwise                = primes' ps ns

    divides q p = q `mod` p == 0

primepowers 0 = []
primepowers n = merge (primepowers (n-1)) [ p^n | p <- primes ]
