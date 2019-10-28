module Sort1 where

insert x [] = [x]
insert x (s : sp)
  | s > x     = x : s : sp
  | otherwise = s : insert x sp

insertSort []       = []
insertSort (s : sp) = insert s (insertSort sp)
