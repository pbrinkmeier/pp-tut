klasse(X, negativ)     :- X < 0, !.
klasse(X, interessant) :- X =< 42, !.
klasse(X, zugross).