package brainfuckc;

abstract class Instruction {
    public abstract <T> T accept(InstructionVisitor<T> visitor);
}
