% modulhandbuch.pl

requires(pse, opruefung).
requires(pse, swt1).

requires(opruefung, la1).
requires(opruefung, gbi).
requires(opruefung, programmieren).

semester(pse, 3).
semester(swt1, 2).
semester(gbi, 1).
semester(programmieren, 1).
semester(la1, 1).

reqT(A, B) :-
  requires(A, C), requires(C, B).
