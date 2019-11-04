module DataExamples2 where

data UserRole = Student | Mitarbeiter | Admin
data StudentId = UAccount String | MatNum Int

data List a = Null | Cons a (List a)
