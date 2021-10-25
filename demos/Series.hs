module Series where

squareSum [] = 0
squareSum (x:xs) = x^2 + squareSum xs
