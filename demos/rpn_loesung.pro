eval(W, OutStack) :- evalRec([], W, OutStack1),
                     reverse(OutStack1, OutStack).
evalRec(Stack, [], Stack).
evalRec(Stack, [N | T], OutStack) :-
    number(N),
    evalRec([N | Stack], T, OutStack).
evalRec(Stack, [Op | T], OutStack) :-
    evalOp(Op, Stack, OutStack1),
    evalRec(OutStack1, T, OutStack).

evalOp(plus, [X, Y | T], [Z | T]) :-
    Z is X + Y.

evalOp(mul, [X, Y | T], [Z | T]) :-
    Z is X * Y.
evalOp(minus, [X, Y | T], [Z | T]) :-
    Z is Y - X.
evalOp(div, [X, Y | T], [Z | T]) :-
    Z is Y / X.

% compile übersetzt einen mathematischen
% Ausdruck nach UPN
compile(N, [N]) :- number(N).
compile(X + Y, L) :-
    compile(X, Xc),
    compile(Y, Yc),
    append(Xc, Yc, Operands),
    append(Operands, [plus], L).
compile(X * Y, L) :-
    compile(X, Xc),
    compile(Y, Yc),
    append(Xc, Yc, Operands),
    append(Operands, [mul], L).
compile(X - Y, L) :-
    compile(X, Xc),
    compile(Y, Yc),
    append(Xc, Yc, Operands),
    append(Operands, [minus], L).
compile(X / Y, L) :-
    compile(X, Xc),
    compile(Y, Yc),
    append(Xc, Yc, Operands),
    append(Operands, [div], L).
