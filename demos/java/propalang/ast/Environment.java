package ast;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class Environment {
    private Program program;
    private Map<String, Integer> map;

    public Environment(Program program) {
        this.program = program;
        this.map = new HashMap<>();
    }

    public Program getProgram() {
        return this.program;
    }

    public void set(String varName, int value) {
        this.map.put(varName, value);
    }

    public int get(String varName) {
        int value = Optional.ofNullable(this.map.get(varName))
            .orElseThrow(() -> new RuntimeException(String.format("%s is not defined in the current scope %s", varName, this)));
        
        return value;
    }

    @Override
    public String toString() {
        return this.map.entrySet().stream().map((entry) -> String.format("%s = %d", entry.getKey(), entry.getValue())).collect(Collectors.joining(", "));
    }
}
