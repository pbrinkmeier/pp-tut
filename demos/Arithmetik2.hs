module Arithmetik2 where

pow3 b e
  | e < 0 = error "e negativ"
  | otherwise = pow3Acc 1 b e
  where
    pow3Acc acc b e
      | e == 0 = acc
      | e `mod` 2 == 0 =
        pow3Acc acc (b * b) (e `div` 2)
      | e `mod` 2 == 1 =
        pow3Acc (b * acc) (b * b) (e `div` 2)
