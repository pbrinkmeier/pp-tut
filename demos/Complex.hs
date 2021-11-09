module Complex where

data Complex = Algebraic Double Double
             | Polar Double Double

real (Algebraic a b) = a
real (Polar r phi)   = r * cos phi
