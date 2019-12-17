% mathematiker_wg.pl

alice(N) :- member(N, [2, 4, 6]).
bob(N) :- member(N, [1, 2, 3, 4, 5, 6, 7]).
carl(N) :- member(N, [1, 2, 3, 4, 5, 6, 7]).

nummerierung(A, B, C) :-
  alice(A),
  bob(B),
  carl(C),
  A =\= B, B =\= C, C =\= A,
  12 =:= A + B + C.
