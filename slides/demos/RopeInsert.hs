module RopeInsert where
import RopeType
import RopeConcat
import RopeSplitAt

ropeInsert :: Int -> Rope -> Rope -> Rope
ropeInsert i toInsert rope =
  ropeL +-+ toInsert +-+ ropeR
  where (ropeL, ropeR) = ropeSplitAt i rope
