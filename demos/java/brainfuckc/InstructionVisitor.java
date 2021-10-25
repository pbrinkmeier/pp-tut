package brainfuckc;

interface InstructionVisitor<T> {
    public T visit(IncrementInstruction incInst);
    public T visit(MoveInstruction movInst);
    public T visit(InputInstruction inpInst);
    public T visit(OutputInstruction outInst);
    public T visit(LoopInstruction loopInst);
}
