module Tut05 (Exp(..), eval, Env) where

import Data.Function (on)
import Data.List (maximumBy)
import Text.Printf (printf)

-- 3.2

next :: Int -> Int
next an
    | even an   = an `quot` 2
    | otherwise = 3 * an + 1

collatz :: Int -> [Int]
collatz = iterate next

num :: Int -> Int
num m = length $ takeWhile (/= 1) $ collatz m

maxNum :: Int -> Int -> (Int, Int)
maxNum a b = foldl maxPair (0, 0) [(m, num m) | m <- [a..b]]
    where
        maxPair (m, n) (m', n')
            | n >= n'   = (m, n)
            | otherwise = (m', n')

maxNum' :: Int -> Int -> (Int, Int)
maxNum' a b = maximumBy (compare `on` snd) [(m, num m) | m <- [a..b]]

answer :: (Int, Int)
answer = maxNum 1 1000

-- 4.1

fun1 xs = (xs == [])
fun2 f a = foldr f "a"
fun3 f a xs c = foldl f a xs c
-- fun4 f xs = map f xs xs
fun5 a b c = (maximum [a..b], 3 * c)
fun6 x y = succ (toEnum (last [fromEnum x..fromEnum y]))
fun7 x = if show x /= [] then x else error

-- 4.2

b2i True = 1
b2i False = 0

data Exp t
    = Var t
    | Const Integer
    | Add (Exp t) (Exp t)
    | Less (Exp t) (Exp t)
    | And (Exp t) (Exp t)
    | Not (Exp t)
    | If (Exp t) (Exp t) (Exp t)

instance Show t => Show (Exp t) where
    show (Var v)       = show v
    show (Const i)     = show i
    show (Add a b)     = printf "(%s + %s)" (show a) (show b)
    show (Less a b)    = printf "(%s < %s)" (show a) (show b)
    show (And a b)     = printf "(%s && %s)" (show a) (show b)
    show (Not e)       = printf "!%s" (show e)
    show (If cond t e) = printf "if %s then %s else %s" (show cond) (show t) (show e)

type Env t = t -> Integer

eval :: Env a -> Exp a -> Integer
eval env (Var v) = env v
eval env (Const i) = i
eval env (Add a b) = eval env a + eval env b
eval env (Less a b)
    | eval env a < eval env b = 1
    | otherwise               = 0
eval env (And a b)
    | eval env a /= 0 && eval env b /= 0 = 1
    | otherwise                          = 0
eval env (Not e)
    | eval env e == 0 = 1
    | otherwise       = 0
eval env (If cond t e)
    | eval env cond /= 0 = eval env t
    | otherwise          = eval env e

clampEnv :: String -> Integer
clampEnv "a"  = 100
clampEnv "lo" = 0
clampEnv "hi" = 42
clampEnv v    = error $ printf "%s is not defined in this env" v

clampExp :: Exp String
clampExp = If (Var "a" `Less` Var "lo") (Var "lo") (If (Not (Var "a" `Less` Var "hi")) (Var "hi") (Var "a"))
