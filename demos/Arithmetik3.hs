module Arithmetik3 where

import Arithmetik2 (pow3)

root exp r
  | exp <= 0  = error "Exponent negativ"
  | r < 0     = error "Wurzel komplex"
  | otherwise = searchRoot 0 (r + 1)
  where
    searchRoot lower upper
      | upper - lower == 1 = lower
      | r < avg `pow3` exp = searchRoot lower avg
      | otherwise          = searchRoot avg upper
      where avg = (lower + upper) `div` 2
