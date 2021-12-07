% mathematiker_wg.pl

alice(2).
alice(4).
alice(6).

bob(B) :- member(B, [1,2,3,4,5,6,7]).
carl(C) :- member(C, [1,2,3,4,5,6,7]).

nummerierung(A, B, C) :-
  alice(A),
  bob(B),
  carl(C),
  A =\= B, B =\= C, C =\= A,
  12 =:= A + B + C.
