module Tut04 where

import Data.Set (Set, fromList, union, delete)

data LambdaTerm
    = Var String
    | App LambdaTerm LambdaTerm
    | Abs String LambdaTerm

lamId = Abs "x" (Var "x")
lamComp = Abs "f" (Abs "g" (Abs "x" (App (Var "f") (App (Var "g") (Var "x")))))
lamEvalAtX = Abs "f" (Var "f" `App` Var "x")

instance Show LambdaTerm where
    show (Var s) = s
    show (App f a) = "(" ++ show f ++ ") (" ++ show a ++ ")"
    show (Abs p b) = "\\" ++ p ++ "." ++ show b

fv :: LambdaTerm -> Set String
fv (Var s) = fromList [s]
fv (App f a) = fv f `union` fv a
fv (Abs p b) = delete p (fv b)

substitute :: (String, LambdaTerm) -> LambdaTerm -> LambdaTerm
substitute (_, b) _
    | fv b /= fromList [] = error "Term contains free vars"
substitute (a, b) (Var v)
    | a == v = b
    | otherwise = Var v
substitute sub (App f x) =
    App (substitute sub f) (substitute sub x)
substitute (a, b) (Abs p c)
    | a == p = Abs p c
    | otherwise = Abs p (substitute (a, b) c)

-- Wiederholung

fibs :: [Integer]
fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

primes :: [Integer]
primes = sieve [2..]
  where sieve []     = []
        sieve (p:xs) = p : sieve (filter (not . multipleOf p) xs)
        multipleOf p x = x `mod` p == 0

merge :: Ord a => [a] -> [a] -> [a]
merge xs []   = xs
merge [] ys   = ys
merge (x : xs) (y : ys)
  | x <= y    = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

primepowers :: Integer -> [Integer]
primepowers n = foldr merge [] [map (^i) primes | i <- [1..n]]
