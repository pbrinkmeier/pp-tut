module DataExamples where

data Bool = True | False

data Category = Jackets | Pants | Shoes
  deriving Show
data Filter
  = InSale
  | IsCategory Category
  | PriceRange Float Float
