module Tut02 where

import Prelude ((==), mod, ($), (*), otherwise, not, reverse, (>))

map f [] = []
map f (x : xs) = f x : map f xs

filter pred [] = []
filter pred (x : xs)
  | pred x    = x : filter pred xs
  | otherwise = filter pred xs

squares = map square
  where square x = x * x

even x = x `mod` 2 == 0
odd x = not $ even x

evens = filter even [0..]
odds = filter odd [0..]

odds' = [ x | x <- [0..], odd x]

foldl f acc []       = acc
foldl f acc (x : xs) = foldl f (f acc x) xs


map2 f list = reverse $ foldl foldFunc [] list
  where
    foldFunc acc x = f x : acc


filter2 pred list = reverse $ foldl foldFunc [] list
  where
    foldFunc acc x
      | pred x    = x : acc
      | otherwise = acc


scanl f acc [] = []
scanl f acc (x : xs) = acc' : scanl f acc' xs
  where
    acc' = f acc x

scanl' f acc (s : sp) = f acc s : scanl' f (f acc s) sp
