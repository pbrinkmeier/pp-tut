module LetXInFx where

x = 42
f = (*2)

y = let x = f x in x
