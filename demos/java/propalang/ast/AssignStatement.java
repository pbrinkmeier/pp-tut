package ast;

import java.util.OptionalInt;

public class AssignStatement extends Statement {
    private final String variable;
    private final Expression expression;

    public AssignStatement(String variable, Expression expression) {
        this.variable = variable;
        this.expression = expression;
    }

    @Override
    public OptionalInt run(Environment scope) {
        scope.set(this.variable, this.expression.eval(scope));
        return OptionalInt.empty();
    }
}
