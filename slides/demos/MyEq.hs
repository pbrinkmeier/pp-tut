module MyEq where

data UserRole = Student | Mitarbeiter

class MyEq a where
  is :: a -> a -> Bool
  
  isnt :: a -> a -> Bool
  x `isnt` y = not (x `is` y)

instance MyEq UserRole where
  Student     `is` Student     = True
  Mitarbeiter `is` Mitarbeiter = True
  _           `is` _           = False
