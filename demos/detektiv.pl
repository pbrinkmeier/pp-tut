% detektiv.pl

aussage(alice, freund(bob)).
aussage(alice, feind(carl)).
...

% Widersprüche

widerspruch(freund(X), feind(X)).
...
