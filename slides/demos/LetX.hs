module LetX where

x = 42
y = let z = 2 * x; x = 100 in z
