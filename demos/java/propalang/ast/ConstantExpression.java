package ast;

public class ConstantExpression extends Expression {
    private int value;

    public ConstantExpression(int value) {
        this.value = value;
    }

    public int eval(Environment scope) {
        return this.value;
    }
}
