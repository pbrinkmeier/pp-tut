module PlayingCard3 where

data PlayingCard = PlayingCard Suit Rank
  deriving (Eq, Ord, Show)

data Suit = Hearts | Diamonds | Clubs | Spades
  deriving (Eq, Ord, Show, Enum)
data Rank
  = Rank7 | Rank8 | Rank9 | Rank10
  | Jack  | Queen | King  | Ace
  deriving (Eq, Ord, Show, Enum)
