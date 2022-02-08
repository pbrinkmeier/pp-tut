package ast;

import java.util.List;

public class CallExpression extends Expression {
    private String functionName;
    private List<Expression> arguments;

    public CallExpression(String functionName, List<Expression> arguments) {
        this.functionName = functionName;
        this.arguments = arguments;
    }

    @Override
    public int eval(Environment scope) {
        Func callee = scope.getProgram().getFunction(this.functionName);
        List<Integer> argumentValues = this.arguments.stream().map((argument) -> argument.eval(scope)).toList();

        return callee.apply(argumentValues, scope.getProgram()).orElse(0);
    }
}
