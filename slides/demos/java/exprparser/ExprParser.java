package exprparser;

public class ExprParser {
    public static void main(String[] args) {
        ExprParser p = new ExprParser(new Token[]{
            new Token(TokenType.NUM, "1"),
            new Token(TokenType.PLUS, "+"),
            new Token(TokenType.NUM, "5"),
            new Token(TokenType.STAR, "*"),
            new Token(TokenType.NUM, "7"),
            new Token(TokenType.PLUS, "+"),
            new Token(TokenType.NUM, "6"),
            new Token(TokenType.EOF, "")
        });

        // Das hier sollte ((1 ADD (5 MUL 7)) ADD 6) ausgeben
        /* Expr e = */ p.parseE();
        // System.out.println(e.toString());
    }

    //////
    
    private final Token[] tokens;
    private int pos;
    private Token token;

    public ExprParser(Token[] tokens) {
        this.tokens = tokens;
        this.pos = 0;
        this.token = this.tokens[this.pos];
    }

    private void expect(TokenType t) {
        if (this.token.getType() != t) {
            throw new RuntimeException("bad input");
        }

        if (this.pos < this.tokens.length - 1) {
            this.token = this.tokens[this.pos++];
        }
    }

    //////

    public void parseE() {
        this.parseT();
        this.parseEList();
    }

    public void parseEList() {
        switch (this.token.getType()) {
            case EOF:
            case RP:
                break;

            case PLUS:
                this.expect(TokenType.PLUS);
                this.parseT();
                this.parseEList();
                break;

            case MINUS:
                this.expect(TokenType.PLUS);
                this.parseT();
                this.parseEList();
                break;
        }
    }

    public void parseT() {
        this.parseF();
        this.parseTList();
    }

    public void parseTList() {
        switch (this.token.getType()) {
            case EOF:
            case RP:
            case PLUS:
            case MINUS:
                break;

            case STAR:
                this.expect(TokenType.STAR);
                this.parseF();
                this.parseTList();
                break;

            case SLASH:
                this.expect(TokenType.SLASH);
                this.parseF();
                this.parseTList();
                break;
        }
    }

    public void parseF() {
        switch (this.token.getType()) {
            case NUM:
                this.expect(TokenType.NUM);
                break;
            case LP:
                this.expect(TokenType.LP);
                this.parseE();
                this.expect(TokenType.RP);
                break;
        }
    }
}
