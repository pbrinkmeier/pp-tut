module AstEval2 where

eval :: Env a -> Exp a -> Integer
eval env (Less e1 e2)
  | eval env e1 < eval env e2 = 1
  | otherwise                 = 0
eval env (And e1 e2)
  | eval env e1 /= 0 && eval env e2 /= 0 = 1
  | otherwise                            = 0
eval env (Not e)
  | not $ eval env e /= 0 = 1
  | otherwise             = 0
