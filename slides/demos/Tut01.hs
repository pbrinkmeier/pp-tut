fak 0 = 1
fak n = n * fak (n-1)

fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

fibs n = reverse (fibsH n)
  where
    fibsH 0 = [0]
    fibsH n = (fib n : fibs (n - 1))
    -- fibsH n (x:xs) = (fibsH (n-1) xs):(fib n):xs

fibs' 0 = [0]
fibs' n = (fibs' (n - 1)) ++ [fib n]

fibs'' n = reverse (fibsH n [])
  where
    fibsH 0 l = l
    fibsH n l = fibsH (n-1) (fib n : l)

fibsTo n = takeWhile (<= n) [fib i | i <- [0..]]
