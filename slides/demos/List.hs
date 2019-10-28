len [] = 0
len (x:xs) = 1 + len xs

sumL [] = 0
sumL (x:xs) = x + sumL xs

concat' :: [[ a ]] -> [ a ]
concat' [] = []
concat' (first : rest) = first ++ (concat rest)

concat'' :: [[a]] -> [a]
concat'' = foldl (++) []

intersperse :: a -> [ a ] -> [ a ]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse sep (first : rest) = (first : (sep : (intersperse sep rest)))

intercalate sep = concat . intersperse sep

head' (first : _) = first
