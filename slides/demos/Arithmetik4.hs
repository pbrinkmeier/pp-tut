module Arithmetik4 where

import Arithmetik3 (pow3)

root exp r
  | exp <= 0  = error "Exponent muss positiv sein"
  | r < 0     = error "Wurzel darf nicht komplex sein"
  | otherwise = searchRoot 0 (r + 1)
  where
    searchRoot lower upper
      | upper - lower == 1 = lower
      | r < avg `pow3` exp = searchRoot lower avg
      | otherwise          = searchRoot avg upper
      where
        avg = (lower + upper) `div` 2
