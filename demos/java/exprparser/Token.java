package exprparser;

public class Token {
    private final TokenType type;
    private final String source;

    public Token(TokenType type, String source) {
        this.type = type;
        this.source = source;
    }

    public TokenType getType() {
        return this.type;
    }

    public String getSource() {
        return this.source;
    }
}
