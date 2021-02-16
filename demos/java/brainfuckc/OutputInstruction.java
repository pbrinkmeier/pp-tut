package brainfuckc;

class OutputInstruction extends Instruction {
    @Override
    public <T> T accept(InstructionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
