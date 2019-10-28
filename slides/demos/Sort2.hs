module Sort2 where

merge listA [] = listA
merge [] listB = listB
merge (a : as) (b : bs)
  | a < b     = (a : merge as (b : bs))
  | otherwise = (b : merge (a : as) bs)

mergeSort []   = []
mergeSort [a]  = [a]
mergeSort list = merge (mergeSort a) (mergeSort b)
  where
    a = take (length list `div` 2) list
    b = drop (length list `div` 2) list
