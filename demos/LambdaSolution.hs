module LambdaSolution where

import Data.Set
import LambdaN -- Contains LambdaTerm type.

-- Simple instance, enough for small terms.
instance Show LambdaTerm where
  show (Var v       ) = v
  show (App f   x   ) = t1 ++ " " ++ t2
    where
      t1 = case f of
        Abs _ _ -> "(" ++ show f ++ ")"
        _       -> show f
      t2 = case x of
        App _ _ -> "(" ++ show x ++ ")"
        Abs _ _ -> "(" ++ show x ++ ")"
        _       -> show x
  show (Abs arg body) = "λ" ++ arg ++ "." ++ (show body)

fv (Var x)   = fromList [x]
fv (App f x) = fv f `union` fv x
fv (Abs p b) = p `delete` fv b

-- Note: Doesn't avoid capture!
substitute (s, t) (Var x)
  | s == x    = t
  | otherwise = Var x
substitute subst (App f x) = App (substitute subst f) (substitute subst x)
substitute (s, t) (Abs p b)
  | s == p    = Abs p b
  | otherwise = Abs p (substitute (s, t) b)
