sum a b f
    | a > b = 0
    | otherwise = f a + sum (a+1) b f
-- Bspw. sum 1 10 id == 55
