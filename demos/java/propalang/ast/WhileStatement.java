package ast;

import java.util.OptionalInt;

public class WhileStatement extends Statement {
    private final Expression loopCondition;
    private final Statement loopBody;

    public WhileStatement(Expression loopCondition, Statement loopBody) {
        this.loopCondition = loopCondition;
        this.loopBody = loopBody;
    }

    @Override
    public OptionalInt run(Environment scope) {
        while (this.loopCondition.eval(scope) != 0) {
            OptionalInt result = this.loopBody.run(scope);
            if (result.isPresent()) {
                return result;
            }
        }

        return OptionalInt.empty();
    }
}