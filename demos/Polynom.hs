module Polynom where

type Polynom = [Double]

cmult polynom c = map (* c) polynom

eval polynom x = foldr go 0 polynom
  where go a_n acc = acc * x + a_n

deriv [] = []
deriv polynom = zipWith (*) [1..] $ tail polynom
