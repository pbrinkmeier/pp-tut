module List where

data List a = Null | Cons a (List a)
    deriving (Show)

map' f Null = Null
map' f (Cons x xs) = Cons (f x) (map' f xs)
