package ast;

import java.util.OptionalInt;

public class PrintStatement extends Statement {
    private Expression expression;

    public PrintStatement(Expression expression) {
        this.expression = expression;
    }

    @Override
    public OptionalInt run(Environment scope) {
        System.out.println(this.expression.eval(scope));
        return OptionalInt.empty();
    }
}
