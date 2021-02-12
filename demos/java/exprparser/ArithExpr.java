package exprparser;

public class ArithExpr extends Expr {
    private final ArithExpr.OpType opType;
    private final Expr lhs;
    private final Expr rhs;

    public ArithExpr(ArithExpr.OpType opType, Expr lhs, Expr rhs) {
        this.opType = opType;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    @Override
    public String toString() {
        return String.format("(%s %s %s)", this.lhs, this.opType, this.rhs);
    }

    //////
    
    public static enum OpType {
        ADD,
        SUB,
        MUL,
        DIV
    }
}
