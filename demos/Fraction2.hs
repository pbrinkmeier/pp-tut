-- stack script --install-ghc --resolver lts-18.14

module Fraction2 where

import Test.Framework (defaultMainWithArgs, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit ((@?=))

-- Implementation
-- gcd' = gcd
gcd' a b = error "Not implemented"

data Fraction = Fraction Integer Integer
    deriving (Show, Eq)

add (Fraction a b) (Fraction a' b') =
    error "Not implemented"

mul (Fraction a b) (Fraction a' b') =
    Fraction (a * a') (b * b')

instance Num Fraction where
    (+) = add
    (*) = mul
    abs (Fraction a b) = Fraction (abs a) (abs b)
    signum (Fraction a b) = Fraction (signum a * signum b) 1
    negate (Fraction a b) = Fraction (-a) b

-- Testing

main = defaultMainWithArgs tests ["--timeout=5"]

tests =
    [ testCase "mul correctly multiplies 6 and 7" $ mul (Fraction 6 1) (Fraction 7 1) @?= (Fraction 42 1)
    , testCase "gcd' finds greatest common divisor of 120 and 45" $ gcd' 120 45 @?= 15
    , testGroup "gcd'" [ testCase "agrees with Prelude.gcd" $ gcd' a b @?= gcd a b | (a, b) <- gcdInputs]
    ]
    where
        gcdInputs = [(120, 45), (99, 32)] ++ [(a, b) | a <- [1..10], b <- [1..10]]
