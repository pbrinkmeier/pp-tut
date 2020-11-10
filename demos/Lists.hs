module Lists where

sumL :: [Int] -> Int
sumL [] = 0
sumL (first : rest) = first + (sumL rest)
