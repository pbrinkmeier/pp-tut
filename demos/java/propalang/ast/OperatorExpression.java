package ast;

public class OperatorExpression extends Expression {
    private final Operator operator;
    private final Expression a;
    private final Expression b;

    public OperatorExpression(Operator operator, Expression a, Expression b) {
        this.operator = operator;
        this.a = a;
        this.b = b;
    }

    @Override
    public int eval(Environment scope) {
        int aValue = a.eval(scope);
        int bValue = b.eval(scope);

        switch (this.operator) {
            case ADD:
                return aValue + bValue;
            case SUBTRACT:
                return aValue - bValue;
            case MULTIPLY:
                return aValue * bValue;
            case DIVIDE:
                return aValue / bValue;
            case LESS_THAN:
                return aValue < bValue ? 1 : 0;
            case EQUALS:
                return aValue == bValue ? 1 : 0;
            default:
                throw new RuntimeException(String.format("Operator %s not implemented", this.operator));
        }
    }
}
