module Sort1 where

insert x [] = [x]
insert x (y:ys)
  | x <= y    = x : y : ys
  | otherwise = y : insert x ys

insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

insertSort' :: Ord a => [a] -> [a]
insertSort' = foldr insert []
