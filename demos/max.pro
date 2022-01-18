max(A, B, C) :- A >  B, !, C = A.
max(A, B, C) :- A =< B, !, C = B.