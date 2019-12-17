keinPutzdienstFuer(L, K, P, X) :-
  Cd is (K - 1),
  helper(L, Cd, K, P, X).

helper([X], Cd, K, [], X) :-
  !.
helper([H | T], 0, K, [H | P], X) :-
  K2 is (K - 1),
  helper(T, K2, K, P, X),
  !.
helper([H | T], Cd, K, P, X) :-
  Cd2 is (Cd - 1),
  append(T, [H], T2),
  helper(T2, Cd2, K, P, X).

range(X, Y, []) :- X >= Y.
range(X, Y, [X | T]) :-
  X < Y,
  X2 is X + 1,
  range(X2, Y, T).
