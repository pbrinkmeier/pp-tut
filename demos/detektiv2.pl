taeter(T) :-
  delete([alice, bob, carl], T, Rest),
  not(inkonsistent(Rest)).

inkonsistent(Zeugen) :- ...
