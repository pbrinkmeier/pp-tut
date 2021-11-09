module PlayingCard2 where
import PlayingCard
instance Eq Suit where
  Hearts   == Hearts   = True
  Diamonds == Diamonds = True
  Clubs    == Clubs    = True
  Spades   == Spades   = True
  _        == _        = False
instance Ord Suit where
  s1 <= s2 = toInt s1 <= toInt s2
    where toInt Hearts   = 0
          toInt Diamonds = 1
          toInt Clubs    = 2
          toInt Spades   = 3
