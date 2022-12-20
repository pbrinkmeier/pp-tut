% compile übersetzt einen mathematischen
% Ausdruck nach UPN
compile(N, [N]) :- number(N).
compile(X + Y, L) :-
    compile(X, Xc),
    compile(Y, Yc),
    ...
