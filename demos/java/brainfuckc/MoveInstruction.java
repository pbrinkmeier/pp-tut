package brainfuckc;

class MoveInstruction extends Instruction {
    public final int movement;

    public MoveInstruction(int m) {
        this.movement = m;
    }

    @Override
    public <T> T accept(InstructionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
