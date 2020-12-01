module LamTerm where

data LamTerm
  = Var String
  | Lam String LamTerm
  | App LamTerm LamTerm
