module ChurchNumbers where

type Church t = (t -> t) -> t -> t

int2church n f t = iterate f t !! n

-- Rekursiv:
int2church' 0 f t = t
int2church' n f t = f $ int2church (n - 1) f t

church2int cn = cn (+ 1) 0
