module AstShow where
import AstType

instance Show t => Show (Exp t) where
  show (Const c) = show c
  show (Var   v) = show v -- Darf man wegen Show t
  show (Add a b) =
    "(" ++ show a ++ " + " ++ show b ++ ")"
-- etc.
