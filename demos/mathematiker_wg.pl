% mathematiker_wg.pl

alice(2).
alice(4).
alice(6).
...

nummerierung(A, B, C) :-
  alice(A),
  bob(B),
  carl(C),
  ...
  12 =:= A + B + C.
