module Lambda where

import Data.Set

data LambdaTerm
  = Var String
  | App LambdaTerm LambdaTerm
  | Abs String LambdaTerm

instance Show LambdaTerm where
  show (Var v       ) = v
  show (App f   x   ) = t1 ++ " " ++ t2
    where
      t1 = case f of
        Abs _ _ -> "(" ++ show f ++ ")"
        _       ->        show f
      t2 = case x of
        App _ _ -> "(" ++ show x ++ ")"
        Abs _ _ -> "(" ++ show x ++ ")"
        _       ->        show x
  show (Abs arg body) = "λ" ++ arg ++ "." ++ (show body)

fv (Var s) = fromList [s]
fv (App f a) = fv f `union` fv a
fv (Abs p b) = delete p $ fv b

-- alpha equivalence
instance Eq LambdaTerm where
  (Var x)     == (Var y)     = x == y
  (App f1 x1) == (App f2 x2) = f1 == f2 && x1 == x2
  (Abs a1 b1) == (Abs a2 b2)
    | a1 == a2               = b1 == b2
    | not (a1 `elem` fv b2)  = b1 == applySubst (a2 +> Var a1) b2
    | otherwise              = False
  _           == _           = False

type Substitution = (String, LambdaTerm)
v +> t = (v, t)

applySubst :: Substitution -> LambdaTerm -> LambdaTerm
applySubst (replaceVar, replaceTerm) (Var var)
  | var == replaceVar = replaceTerm
  | otherwise         = Var var

applySubst s (App f x) = App (applySubst s f) (applySubst s x)

applySubst (replaceVar, replaceTerm) (Abs arg body)
  | arg == replaceVar = Abs arg body
  | otherwise         = Abs arg $ applySubst (replaceVar, replaceTerm) $ body

betaReduction (App (Abs x b) arg) = applySubst (x +> arg) b
betaReduction (App f arg)
  | f == f'                       = App f $ betaReduction arg
  | otherwise                     = App f' arg
  where f' = betaReduction f
betaReduction (Abs x b)           = Abs x $ betaReduction b
betaReduction x                   = x

evalHistory :: LambdaTerm -> IO ()
evalHistory term = evalHistory' [term] term
  where
    evalHistory' hist term = do
      putStrLn $ show term
      let term' = betaReduction term
      
      if not (term' `elem` hist) then
        evalHistory' (term' : hist) term'
      else
        return ()
