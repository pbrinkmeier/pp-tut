module RopeSplitAt where
import RopeType
import RopeConcat

ropeSplitAt :: Int -> Rope -> (Rope, Rope)
ropeSplitAt i (Leaf s)      = (Leaf sl, Leaf sr)
  where (sl, sr) = (take i s, drop i s)
ropeSplitAt i (Inner l w r)
  | i < w                   = (ll, lr +-+ r)
  | i > w                   = (l +-+ rl, rr)
  | otherwise               = (l, r)
  where (ll, lr) = ropeSplitAt i       l
        (rl, rr) = ropeSplitAt (i - w) r
