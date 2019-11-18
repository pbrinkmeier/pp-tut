module AstEval2 where

eval :: Env a -> Exp a -> Integer
eval env (Less e1 e2) = b2i $
  (eval env e1) < (eval env e2)
eval env (And e1 e2) = b2i $
  (i2b $ eval env e1) && (i2b $ eval env e2)
eval env (Not e) = b2i $ not $ i2b $ eval env e

b2i b = if b then 0 else 1
i2b i = if i == 0 then False else True
