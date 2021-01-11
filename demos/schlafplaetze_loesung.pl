bett(X) :-
  member(X, [1, 2, 3, 4, 5]).

schlafplaetze(A, B, C, D, E) :-
  bett(A),
  bett(B),
  bett(C),
  bett(D),
  bett(E),
  distinct([A, B, C, D, E]),
  A =\= 5,
  B =\= 1,
  C =\= 1, C =\= 5,
  D > B,
  mynot(adjacent(B, C)),
  mynot(adjacent(E, C)).

mynot(X) :-
  X,
  !,
  0 > 0.
mynot(X).

adjacent(A, B) :-
  A - B =:= 1.
adjacent(A, B) :-
  B - A =:= 1.

distinct([]).
distinct([X | T]) :-
  mynot(member(X, T)),
  distinct(T).
