module RopeType where

data Rope
  = Leaf String
  | Inner Rope Int Rope
  deriving Show

toStr :: Rope -> String
toStr (Leaf s)      = s
toStr (Inner l _ r) = toStr l ++ toStr r

-- Examples
r1 = Leaf "Hello, World!"
r2 = Inner "String: " 8 r1
