package ast;

import java.util.List;
import java.util.Map;
import java.util.OptionalInt;

public class Func {
    private final String name;
    private final List<Parameter> parameters;
    private final Block body;

    public Func(String name, List<Parameter> parameters, Block body) {
        this.name = name;
        this.parameters = parameters;
        this.body = body;
    }

    public String getName() {
        return this.name;
    }

    public OptionalInt apply(List<Integer> arguments, Program program) {
        if (arguments.size() != this.parameters.size()) {
            throw new RuntimeException(String.format("Needs %d arguments for %s (%s given)", this.parameters.size(), this.name, arguments.size()));
        }

        Environment funcScope = new Environment(program);

        for (int i = 0; i < this.parameters.size(); i++) {
            funcScope.set(this.parameters.get(i).getName(), arguments.get(i));
        }

        return this.body.run(funcScope);
    }
}
