package ast;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalInt;

public class Program {
    private final Map<String, Func> functions;

    public Program(List<Func> functions) {
        this.functions = new HashMap<>();
        
        for (Func func: functions) {
            this.functions.put(func.getName(), func);
        }
    }

    public Func getFunction(String name) {
        return Optional.ofNullable(this.functions.get(name))
            .orElseThrow(() -> new RuntimeException(String.format("Function %s is not defined", name)));
    }

    public OptionalInt run() {
        return this.getFunction("main").apply(Arrays.asList(), this);
    }
}
