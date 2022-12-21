% putzdienst.pl

% Bspw.
% ?- keinPutzdienstFuer([a, b, c, d, e], 2, X)
keinPutzdienstFuer(L, K, X) :-
  helper(L, K, K, X).

helper([X], _C, _K, X) :- !.
helper([H|T], 1, K, X) :- ...
...
