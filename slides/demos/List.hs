module List where

data List a = Null | Cons a (List a)

map' f Null = Null
map' f (Cons x xs) = Cons x (map f xs)
