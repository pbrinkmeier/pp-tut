package ast;

public abstract class Expression {
    public abstract int eval(Environment scope);
}
