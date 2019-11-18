module TypeClassExamples where

-- Ersatz für null in C-likes
-- Auch bekannt als "Maybe"
data Optional a = Present a | NoValue

instance Show a => Show (Optional a) where
  show (Present x) = show x
  show NoValue     = "null"
