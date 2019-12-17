% detektiv.pl

aussage(alice, freund(bob)).
aussage(alice, feind(carl)).

aussage(bob, unterwegs(bob)).
aussage(bob, fremder(bob)).

aussage(carl, daheim(alice)).
aussage(carl, daheim(bob)).
aussage(carl, daheim(carl)).

% Widersprüche

widerspruch(freund(X), feind(X)).
widerspruch(feind(X), fremder(X)).
widerspruch(fremder(X), freund(X)).

widerspruch(unterwegs(X), daheim(X)).

taeter(T) :-
  select(T, [alice, bob, carl], Rest),
  not(inkonsistent(Rest)).

inkonsistent(L) :-
  member(A, L),
  member(B, L),
  not(A = B),
  aussage(A, AA),
  aussage(B, AB),
  widerspruch(AA, AB).
