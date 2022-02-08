package parser;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public class PropaLangLexer {
    private static final Map<String, TokenType> KEYWORDS = new HashMap<>();
    static {
        KEYWORDS.put("func", TokenType.FUNC);
        KEYWORDS.put("if", TokenType.IF);
        KEYWORDS.put("else", TokenType.ELSE);
        KEYWORDS.put("while", TokenType.WHILE);
        KEYWORDS.put("return", TokenType.RETURN);
        KEYWORDS.put("print", TokenType.PRINT);
        KEYWORDS.put("for", TokenType.FOR);
    }

    private int oldPosition;
    private int position;
    private final String source;

    public PropaLangLexer(String source) {
        this.oldPosition = 0;
        this.position = 0;
        this.source = source;
    }

    private boolean isEof() {
        return this.position >= this.source.length();
    }

    // Will throw ArrayIndexOutOfBounds if this.isEof()
    private char getLookahead() {
        return this.source.charAt(this.position);
    }

    private void advance() {
        this.position++;
    }

    private Token createToken(TokenType type) {
        Token t = new Token(type, this.text());
        return t;
    }

    private String text() {
        return this.source.substring(this.oldPosition, this.position);
    }

    public RuntimeException error(String message) {
        return new RuntimeException(String.format("%s at %s", message, this.source.substring(this.oldPosition)));
    }

    public Token lex() {
        // ship whitespace
        while (!this.isEof() && isWhitespace(this.getLookahead())) {
            this.advance();
        }
        this.oldPosition = this.position;

        if (this.isEof()) {
            return this.createToken(TokenType.EOF);
        }

        if (isIdentifierChar(this.getLookahead())) {
            while (!this.isEof() && isIdentifierChar(this.getLookahead())) {
                this.advance();
            }

            return this.createToken(Optional.ofNullable(KEYWORDS.get(this.text())).orElse(TokenType.IDENTIFIER));
        }

        if (isDigit(this.getLookahead())) {
            while (!this.isEof() && isDigit(this.getLookahead())) {
                this.advance();
            }

            return this.createToken(TokenType.INTEGER_LITERAL);
        }

        switch (this.getLookahead()) {
            case '{':
                this.advance();
                return this.createToken(TokenType.START_BLOCK);
            case '}':
                this.advance();
                return this.createToken(TokenType.END_BLOCK);
            case '(':
                this.advance();
                return this.createToken(TokenType.LEFT_PAREN);
            case ')':
                this.advance();
                return this.createToken(TokenType.RIGHT_PAREN);
            case ',':
                this.advance();
                return this.createToken(TokenType.COMMA);
            case '=':
                this.advance();
                if (!this.isEof() && this.getLookahead() == '=') {
                    this.advance();
                    return this.createToken(TokenType.EQUALS);
                } else {
                    return this.createToken(TokenType.ASSIGN);
                }
            case '<':
                this.advance();
                return this.createToken(TokenType.LESS_THAN);
            case '+':
                this.advance();
                return this.createToken(TokenType.PLUS);
            case '-':
                this.advance();
                return this.createToken(TokenType.MINUS);
            case '*':
                this.advance();
                return this.createToken(TokenType.STAR);
            case ';':
                this.advance();
                return this.createToken(TokenType.SEMICOLON);
            case '/':
                this.advance();
                return this.createToken(TokenType.SLASH);
        }

        throw this.error("Lexer error");
    }

    private static boolean isWhitespace(char c) {
        return c == ' ' || c == '\n' || c == '\r' || c == '\t';
    }

    private static boolean isIdentifierChar(char c) {
        return c == '_' || (c >= 'a' && c <= 'z');
    }

    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }
}
