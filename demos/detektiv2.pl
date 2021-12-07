taeter(T) :-
  select(T, [alice, bob, carl], Rest),
  not(inkonsistent(Rest)).

inkonsistent(Zeugen) :- ...
