% putzdienst.pl

% Bspw.
% ?- keinPutzdienstFuer([a, b, c, d, e], 2, X)
keinPutzdienstFuer(L, K, X) :-
  Countdown is K - 1,
  helper(L, Countdown, K, X).

helper([X], _C, _K, X) :- !.
...
