klasse(X, negativ)     :- X < 0, !.
klasse(X, interessant) :- X >= 0, X =< 42, !.
klasse(X, zugross)     :- X > 42.