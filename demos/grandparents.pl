grandparent(X, Y) :- parent(X, Z), parent(Z, Y).
parent(X, Y) :- mother(X, Y).
parent(X, Y) :- father(X, Y).

mother(inge, emil).
mother(inge, petra).
father(emil, kunibert).
