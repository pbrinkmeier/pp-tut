module Fraction

data Fraction = Fraction Integer Integer

mul (Fraction a b) (Fraction a' b') =
    Fraction (a * a') (b * b')
