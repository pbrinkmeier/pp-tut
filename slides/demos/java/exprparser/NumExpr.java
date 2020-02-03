package exprparser;

public class NumExpr extends Expr {
    private final int value;

    public NumExpr(int value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return String.format("%d", this.value);
    }
}
