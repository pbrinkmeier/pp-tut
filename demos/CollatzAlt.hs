module CollatzAlt where

import Collatz (num)
import Data.Function (on)
import Data.List (maximumBy)

maxNum a b =
  maximumBy
    (compare `on` snd)
    [(m, num m) | m <- [a..b]]
