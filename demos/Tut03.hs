module Tut where

import Data.Ratio (numerator, denominator)

f :: a -> a -> a
f x y = x

g :: a -> a -> a
g x y = y

data Shape
  = Circle Double
  | Rectangle Double Double
  deriving (Eq, Show)

data SortBy = Price | Size | Memory | CPUFrequency

data PlayingCard = PlayingCard Suit Rank
  deriving (Eq, Ord)

data Suit = Spades | Hearts | Clubs | Diamonds
  deriving (Eq, Ord, Enum, Show)

data Rank
  = R7 | R8 | R9 | R10
  | Jack | Queen | King | Ace
  deriving (Eq, Ord, Enum)

instance Show Rank where
  show R7 = "7"
  show R8 = "8"
  show R9 = "9"
  show R10 = "10"
  show Jack = "Jack"
  show Queen = "Queen"
  show King = "King"
  show Ace = "Ace"

instance Show PlayingCard where
  show (PlayingCard suit rank) =
    show rank ++ " of " ++ show suit

allCards = [ PlayingCard suit rank
           | suit <- [Spades .. Diamonds]
           , rank <- [R7 .. Ace]
           ]

data Fraction = Fraction Integer Integer

instance Eq Fraction where
  Fraction n d == Fraction n' d' =
    n == n' && d == d'

newFraction :: Integer -> Integer -> Fraction
newFraction numer denom = normalize (Fraction numer denom)

add :: Fraction -> Fraction -> Fraction
add (Fraction n d) (Fraction n' d') =
  newFraction (n * d' + n' * d) (d * d')

mul :: Fraction -> Fraction -> Fraction
mul (Fraction n d) (Fraction n' d') =
  newFraction (n * n') (d * d')

instance Show Fraction where
  show (Fraction n d) =
    show n ++ "/" ++ show d

instance Num Fraction where
  (+) = add
  (*) = mul
  abs (Fraction n d) = newFraction (abs n) d
  signum (Fraction n _) = newFraction (signum n) 1
  fromInteger i = newFraction i 1
  negate (Fraction n d) = newFraction (-n) d

instance Fractional Fraction where
  recip (Fraction n d) = newFraction d n
  fromRational r = newFraction (numerator r) (denominator r)

normalize :: Fraction -> Fraction
normalize (Fraction numer denom)
    | denom' < 0 = Fraction (-numer') (-denom')
    | otherwise  = Fraction numer' denom'
    where
        numer' = numer `quot` gcd numer denom
        denom' = denom `quot` gcd numer denom
