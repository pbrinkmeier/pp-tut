f y = \z -> x + 7 * z - y
x = 1
g x = x + (
  let
    y = x * 2; x = 5 * 5
  in (let x = f x 2 in x + y))
h = let z = 2 in g x + (\z -> -z) z where z = 3
