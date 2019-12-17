% schlafplaetze.pl

bett(X) :- member(X, [1, 2, 3, 4, 5]).

schlafplaetze(A, B, C, D, E) :-
  bett(A), bett(B), bett(C), bett(D), bett(E),
  distinct([A, B, C, D, E]),
  A =\= 5,
  B =\= 1,
  C =\= 1,
  C =\= 5,
  D > B,
  not(adjacent(B, C)),
  not(adjacent(E, C)).

adjacent(A, B) :- A - B =:= 1.
adjacent(A, B) :- B - A =:= 1.

distinct([]).
distinct([X | Xs]) :-
  not(member(X, Xs)), distinct(Xs).
