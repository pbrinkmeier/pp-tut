module Collatz where

collatz = iterate next
  where next aN | even aN   = aN `div` 2
                | otherwise = 3 * aN + 1

num = length . takeWhile (/= 1) . collatz

maxNum a b = bestNum [(m, num m) | m <- [a..b]]
  where bestNum = foldl maxSecond (0, 0)
        maxSecond a b
          | snd a >= snd b = a
          | otherwise      = b
