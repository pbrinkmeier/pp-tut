klasse(X, K)     :- X < 0, !, K = negativ.
klasse(X, K) :- X =< 42, !, K = interessant.
klasse(X, zugross).
