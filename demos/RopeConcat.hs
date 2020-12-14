module RopeConcat where
import RopeType
import RopeLength

ropeConcat :: Rope -> Rope -> Rope
ropeConcat r1 r2 = Inner r1 (ropeLength r1) r2

(+-+) = ropeConcat
