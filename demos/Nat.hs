module Nat (Nat, zero, inc, dec, isZero) where

newtype Nat = Nat Integer

instance Show Nat where
    show (Nat x) = show x

zero :: Nat
zero = Nat 0

inc :: Nat -> Nat
inc (Nat x) = Nat (x + 1)

dec :: Nat -> Nat
dec (Nat x) = Nat (max 0 (x - 1))

isZero :: Nat -> Bool
isZero (Nat x) = x == 0
