package brainfuckc;

import java.util.List;

class LoopInstruction extends Instruction {
    public final List<Instruction> instructions;

    public LoopInstruction(List<Instruction> is) {
        this.instructions = is;
    }

    @Override
    public <T> T accept(InstructionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
