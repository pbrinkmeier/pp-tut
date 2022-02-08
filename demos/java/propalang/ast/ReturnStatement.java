package ast;

import java.util.OptionalInt;

public class ReturnStatement extends Statement {
    private Expression expression;

    public ReturnStatement(Expression expression) {
        this.expression = expression;
    }

    @Override
    public OptionalInt run(Environment scope) {
        return OptionalInt.of(this.expression.eval(scope));
    }
}
