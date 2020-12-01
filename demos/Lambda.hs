module Lambda where

data LambdaTerm
  = Var String  -- Variable
  | App () ()   -- Funktionsanwendung: f a
  | Abs () ()   -- Abstraktion: \p.b
