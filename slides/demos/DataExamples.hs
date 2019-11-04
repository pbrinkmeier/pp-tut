module DataExamples where

data Bool = True | False

data Category = Jackets | Pants | Shoes
data Filter
  = InSale
  | IsCategory Category
  | PriceRange Float Float
