digits :: Int -> [Int]
digits n
  -- Special cases are handled here.
  | n < 0     = error "need positive number"
  | n == 0    = [0]
  -- digits' is the general solution for positive numbers.
  | otherwise = digits' n
  where
    digits' 0 = []
    digits' n = digits' q ++ [r]
      where q = n `div` 10
            r = n `mod` 10
