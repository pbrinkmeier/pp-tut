module PlayingCards where

data Card = Card Rank Suit deriving (Eq, Ord)
data Suit = Spades | Hearts | Diamonds | Clubs
          deriving (Eq, Ord)
data Rank = Seven | Eight | Nine | Ten
          | Jack | Queen | King | Ace
          deriving (Eq, Ord)
