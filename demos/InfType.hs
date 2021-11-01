module InfType where

-- around "hi" '+' == "+hi+"
around list d = d ++ list ++ [d]
