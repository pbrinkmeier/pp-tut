package brainfuckc;

class IncrementInstruction extends Instruction {
    public final int increment;

    public IncrementInstruction(int i) {
        this.increment = i;
    }

    @Override
    public <T> T accept(InstructionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
