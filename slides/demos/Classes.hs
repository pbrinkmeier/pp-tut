module Classes where

max :: Ord a => a -> a -> a
max x y
  | x > y     = x
  | otherwise = y

findIndex :: Eq a => a -> [a] -> Int
findIndex element (x : xs)
  | x == element = 0
  | otherwise    = 1 + findIndex element xs
