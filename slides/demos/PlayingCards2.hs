module PlayingCards where

data Card = Card Rank Suit deriving Eq
data Suit = Spades | Hearts | Diamonds | Clubs
          deriving (Eq, Ord)
data Rank = Seven | Eight | Nine | Ten
          | Jack | Queen | King | Ace
          deriving (Eq, Ord)

instance Ord Card where
  (Card r1 s1) <= (Card r2 s2) = r1 <= r2 || s1 <= s2
