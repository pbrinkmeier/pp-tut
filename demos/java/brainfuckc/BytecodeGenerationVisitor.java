package brainfuckc;

class BytecodeGenerationVisitor implements InstructionVisitor<Void> {
    private int label = 0;

    // increments the current cell
    // array: var 1
    // index: var 2
    public Void visit(IncrementInstruction incInst) {
        System.out.println(
            String.format("  ; INCREMENT %d\n", incInst.increment) +
            "  aload_1\n" +
            "  iload_2\n" +
            "  \n" +
            "  aload_1\n" +
            "  iload_2\n" +
            "  \n" +
            "  caload\n" +
            String.format("  ldc %d\n", incInst.increment) +
            "  iadd\n" +
            "  castore"
        );

        return null;
    }

    // increments the current index
    public Void visit(MoveInstruction moveInst) {
        System.out.println(
            String.format("  ; MOVE %d\n", moveInst.movement) +
            "  iload_2\n" +
            String.format("  ldc %d\n", moveInst.movement) +
            "  iadd\n" +
            "  istore_2"
        );

        return null;
    }

    public Void visit(InputInstruction inpInst) {
        System.out.println(
            "  ; INPUT\n" +
            "  aload_1\n" +
            "  iload_2\n" +
            "  getstatic java/lang/System/in Ljava/io/InputStream;\n" +
            "  invokevirtual java/io/InputStream/read()I\n" +
            "  castore"
        );

        return null;
    }

    public Void visit(OutputInstruction outInst) {
        System.out.println(
            "  ; OUTPUT\n" +
            "  getstatic java/lang/System/out Ljava/io/PrintStream;\n" +
            "  aload_1\n" +
            "  iload_2\n" +
            "  caload\n" +
            "  invokevirtual java/io/PrintStream/print(C)V"
        );

        return null;
    }

    public Void visit(LoopInstruction loopInst) {
        int start = this.label++;
        int end = this.label++;

        System.out.println(
            "  ; LOOP START\n" +
            String.format("  label_%d:\n", start) +
            "  aload_1\n" +
            "  iload_2\n" +
            "  caload\n" +
            "  iconst_0\n" +
            String.format("  if_icmpeq label_%d\n", end)
        );

        for (Instruction inst: loopInst.instructions) {
            inst.accept(this);
        }

        System.out.println(
            "  ; LOOP END\n" +
            String.format("  goto label_%d\n", start) +
            String.format("  label_%d:\n", end)
        );

        return null;
    }
}
