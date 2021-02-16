package brainfuckc;

import java.util.List;

public class BrainfuckC {
    public static void main(String[] args) {
        // String source = "++++++++[>++++++++<-]>+.+."; // Zeigt "AB"
        // String source = ",>+++[<.>-]"; // Liest Buchstabe und gibt ihn dreimal aus
        String source = args[0];
        List<Instruction> prog = new Parser(source).parseProgram();

        BrainfuckC.generateBytecode(prog);
    }

    public static void generateBytecode(List<Instruction> prog) {
        BytecodeGenerationVisitor v = new BytecodeGenerationVisitor();

        System.out.println(
            ".source Brainfuck.java\n" +
            ".class public Brainfuck\n" +
            ".super java/lang/Object\n" +
            ".method public static main([Ljava/lang/String;)V\n" +
            "  .limit stack 10\n" +
            "  .limit locals 10\n" +
            "  ldc 100000\n" +
            "  istore_2\n" +
            "  ldc 0\n" +
            "  istore_2\n" +
            "  sipush 30000\n" +
            "  newarray char\n" +
            "  astore_1"
        );

        for (Instruction i: prog) {
            i.accept(v);
        }

        System.out.println(
            "  return\n" +
            ".end method"
        );
    }
}
