package ast;

public class VariableExpression extends Expression {
    private final String name;

    public VariableExpression(String name) {
        this.name = name;
    }

    @Override
    public int eval(Environment scope) {
        return scope.get(this.name);
    }
}
