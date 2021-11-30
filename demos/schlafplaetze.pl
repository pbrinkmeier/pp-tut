% schlafplaetze.pl

bett(X) :- member(X, [1, 2, 3, 4, 5]).

schlafplaetze(A, B, C, D, E) :-
  bett(A), bett(B), bett(C), bett(D), bett(E),
  distinct([A, B, C, D, E]),
  % weitere Tests
