main :-
  [A, B, C] = [1, 2, 3],
  max(A, C, X),
  Y is X * 2,
  Y > 0,
  not(Y > 10),
  !.
