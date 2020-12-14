module RopeLength where
import RopeType

ropeLength :: Rope -> Int
ropeLength (Leaf s)      = length s
ropeLength (Inner l w r) = w + ropeLength r
