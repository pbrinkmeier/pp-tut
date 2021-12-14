module ChurchNumbers where

type Church t = (t -> t) -> t -> t

int2church 0 = \s z -> z
int2church n = \s z -> s (int2church (n - 1) s z)

church2int cn = cn (+1) 0