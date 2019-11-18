module LambdaShow where

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
