module PlayingCards where

data Card = Card Rank Suit
data Suit = Spades | Hearts | Diamonds | Clubs
data Rank = Seven | Eight | Nine | Ten
          | Jack | Queen | King | Ace
