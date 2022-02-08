package parser;

public enum TokenType {
    EOF,

    // keywords
    FUNC,
    IF,
    ELSE,
    WHILE,
    RETURN,
    PRINT,
    FOR,

    // symbols
    START_BLOCK,
    END_BLOCK,
    LEFT_PAREN,
    RIGHT_PAREN,
    COMMA,
    ASSIGN,
    EQUALS,
    LESS_THAN,
    PLUS,
    MINUS,
    STAR,
    SEMICOLON,
    SLASH,

    // other
    IDENTIFIER,
    INTEGER_LITERAL
}
