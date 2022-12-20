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
