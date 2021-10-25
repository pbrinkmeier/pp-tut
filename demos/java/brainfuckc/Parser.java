package brainfuckc;

import java.util.ArrayList;
import java.util.List;

class Parser {
    private String source;
    int pos;

    public Parser(String s) {
        this.source = s;
        this.pos = 0;
    }

    public List<Instruction> parseProgram() {
        List<Instruction> instructions = new ArrayList<>();

        while (true) {
            switch (this.token()) {
                case '+':
                case '-':
                case '>':
                case '<':
                case ',':
                case '.':
                case '[':
                    instructions.add(this.parseInstruction());
                    break;
                case ']':
                case 0:
                    return instructions;

                default:
                    throw new RuntimeException("Invalid program");
            }
        }
    }

    private Instruction parseInstruction() {
        Instruction inst;

        switch (this.token()) {
            case '+':
                inst = new IncrementInstruction(1);
                this.next();
                return inst;
            case '-':
                inst = new IncrementInstruction(-1);
                this.next();
                return inst;
            case '>':
                inst = new MoveInstruction(1);
                this.next();
                return inst;
            case '<':
                inst = new MoveInstruction(-1);
                this.next();
                return inst;
            case ',':
                inst = new InputInstruction();
                this.next();
                return inst;
            case '.':
                inst = new OutputInstruction();
                this.next();
                return inst;
            case '[':
                this.next();
                inst = new LoopInstruction(this.parseProgram());
                this.expect(']');
                return inst;
                
            default:
                throw new RuntimeException("Expected an instruction");
        }
    }

    //

    private char token() {
        if (this.pos >= this.source.length()) {
            return 0; // replacement for EOF
        }

        return this.source.charAt(this.pos);
    }

    private void next() {
        this.pos++;
    }

    private void expect(char c) {
        if (this.token() != c) {
            throw new RuntimeException("Unexpected token");
        }
        this.next();
    }
}
