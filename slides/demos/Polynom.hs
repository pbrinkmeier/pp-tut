module Polynom where

type Polynom = [Double]

cmult :: Polynom -> Double -> Polynom
cmult poly c = map (* c) poly

eval :: Polynom -> Double -> Double
eval poly x = foldr evalFold 0 poly
  where evalFold aN acc = aN + x * acc

deriv :: Polynom -> Polynom
deriv [] = []
deriv poly = zipWith (*) [1..] $ tail poly
