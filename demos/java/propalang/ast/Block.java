package ast;

import java.util.List;
import java.util.OptionalInt;

public class Block {
    private final List<Statement> statements;

    public Block(List<Statement> statements) {
        this.statements = statements;
    }

    public OptionalInt run(Environment scope) {
        for (Statement statement: this.statements) {
            OptionalInt returnValue = statement.run(scope);
            if (returnValue.isPresent()) {
                return returnValue;
            }
        }

        return OptionalInt.empty();
    }
}
