module RopeInsert where
import RopeType
import RopeConcat
import RopeSplitAt

ropeDelete :: Int -> Int -> Rope -> Rope
ropeDelete from to rope =
  left +-+ right
  where (left, _ ) = ropeSplitAt from rope
        (_, right) = ropeSplitAt to   rope
