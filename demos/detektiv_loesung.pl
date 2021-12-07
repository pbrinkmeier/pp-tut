% detektiv.pl

aussage(alice, freund(bob)).
aussage(alice, feind(carl)).

aussage(bob, fremd(bob)).
aussage(bob, unterwegs(bob)).

aussage(carl, daheim(alice)).
aussage(carl, daheim(bob)).
aussage(carl, daheim(carl)).

widerspruch(freund(X), feind(X)).
widerspruch(freund(X), fremd(X)).
widerspruch(feind(X), fremd(X)).

widerspruch(unterwegs(X), daheim(X)).

taeter(T) :-
  select(T, [alice, bob, carl], Rest),
  not(inkonsistent(Rest)).

inkonsistent(Zeugen) :-
  member(ZeugeA, Zeugen),
  member(ZeugeB, Zeugen),
  aussage(ZeugeA, A),
  aussage(ZeugeB, B),
  widerspruch(A, B).
