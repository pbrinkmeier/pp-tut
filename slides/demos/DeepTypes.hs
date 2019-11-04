module DeepTypes where

vA  = (\x -> x)     :: a -> a
vB  = (\g x -> g x) :: (a -> b) -> a -> b
vC  = vB            :: (a -> b) -> (a -> b)
vD  = (\x _ -> x)   :: (a -> b -> a)
vE1 = (\x _ -> x)   :: (a -> a -> a)
vE2 = (\_ y -> y)   :: (a -> a -> a)
vF  = []            :: [a]
vG  = [1]           :: [Int]
vH  = []            :: [[a]]
vI  = [[]]          :: [[a]]
-- Alternativ:
-- vA x = x, vB g x = g x, etc.
