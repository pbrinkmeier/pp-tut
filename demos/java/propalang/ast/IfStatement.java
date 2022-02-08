package ast;

import java.util.OptionalInt;

public class IfStatement extends Statement {
    private final Expression condition;
    private final Statement thenStatement;
    private final Statement elseStatement;

    public IfStatement(Expression condition, Statement thenStatement, Statement elseStatement) {
        this.condition = condition;
        this.thenStatement = thenStatement;
        this.elseStatement = elseStatement;
    }

    @Override
    public OptionalInt run(Environment scope) {
        int conditionValue = this.condition.eval(scope);

        if (conditionValue != 0) {
            return this.thenStatement.run(scope);
        } else {
            return this.elseStatement.run(scope);
        }
    }
}
