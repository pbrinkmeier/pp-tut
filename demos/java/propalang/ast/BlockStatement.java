package ast;

import java.util.OptionalInt;

public class BlockStatement extends Statement {
    private final Block block;

    public BlockStatement(Block block) {
        this.block = block;
    }

    @Override
    public OptionalInt run(Environment scope) {
        return this.block.run(scope);
    }
}
