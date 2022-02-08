package ast;

import java.util.OptionalInt;

public abstract class Statement {
    public abstract OptionalInt run(Environment scope);
}
