{-# LANGUAGE FlexibleInstances #-}

module FirstFollow where

import Data.Set (Set, fromList, unions)

-- Terminals and non-terminals
data Any t nt = T t | NT nt
data Grammar t nt = Grammar nt (nt -> [[Any t nt]])

data NonTerminal = Expr | ExprList | Term | TermList | Factor deriving (Eq, Ord)

g'' :: Grammar String NonTerminal
g'' = Grammar Expr p
  where
    p Expr     = [ [ NT Term, NT ExprList ]
                 ]
    p ExprList = [ []
                 , [ T "add", NT Term, NT ExprList ]
                 ]
    p Term     = [ [ NT Factor, NT TermList ]
                 ]
    p TermList = [ []
                 , [ T "mul", NT Factor, NT TermList ]
                 ]
    p Factor   = [ [ T "id" ]
                 , [ T "(", NT Expr, T ")" ]
                 ]

-- Eps a means that a has some kind of "empty value"
class Eps a where
  eps :: a
-- The empty value for strings is the empty string (duh)
instance Eps String where
  eps = ""

first1 :: (Ord t, Eps t) => Grammar t nt -> nt -> Set t
--     vvvvvvvvvvvvvvv this pattern matches on the first argument while preserving the name g
first1 g@(Grammar _ p) s =
  unions $ map rec $ p s
  where
    rec ((T t) : _) = fromList [t]
    rec ((NT v) : _) = first1 g v
    rec [] = fromList [eps]
