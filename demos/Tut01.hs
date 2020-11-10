fac 0 = 1
fac n = n * fac (n - 1)

fib n = fibAcc 0 1 n
  where
    fibAcc a b 0 = a
    fibAcc a b n = fibAcc b (a + b) (n - 1)

fibs n = map fib [0..n]

-- Lösung mit Kombinatoren:
-- fibsTo n = takeWhile (<= n) (map fib [0..])
fibsTo n = fibsTo' 0
  where
    fibsTo' x
      | fib x <= n = fib x : fibsTo' (x + 1)
      | otherwise  = []

productL :: [Int] -> Int
productL = foldr (*) 1

-- Prädikat bei filter: Als Lambda-Funktion...
odds = filter (\x -> x `mod` 2 == 1)

-- ... order lokal definierte Hilfsfunktion.
evens = filter isEven
  where isEven x = x `mod` 2 == 0

squares = map square
  where square x = x * x
