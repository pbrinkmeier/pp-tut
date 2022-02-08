package parser;

import ast.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class PropaLangParser {
    private final PropaLangLexer lexer;
    private Token token;

    public PropaLangParser(String source) {
        this.lexer = new PropaLangLexer(source);
        this.nextToken();
    }

    private Token nextToken() {
        Token oldToken = this.token;
        this.token = this.lexer.lex();
        return oldToken;
    }

    private boolean check(TokenType type) {
        return this.token.getType().equals(type);
    }

    private Token expect(TokenType type) {
        if (!this.token.getType().equals(type)) {
            throw this.lexer.error(String.format("Expected token %s, actual token %s", type, this.token));
        }
        
        return this.nextToken();
    }

    public Program parseProgram() {
        List<Func> functions = new ArrayList<>();

        while (this.check(TokenType.FUNC)) {
            functions.add(this.parseFunc());
        }
        this.expect(TokenType.EOF);

        return new Program(functions);
    }

    public Func parseFunc() {
        this.expect(TokenType.FUNC);
        String name = this.expect(TokenType.IDENTIFIER).getText();
        this.expect(TokenType.LEFT_PAREN);
        List<Parameter> parameters = this.parseParameters();
        this.expect(TokenType.RIGHT_PAREN);
        Block body = this.parseBlock();

        return new Func(name, parameters, body);
    }

    public List<Parameter> parseParameters() {
        List<Parameter> parameters = new ArrayList<>();

        while (true) {
            if (this.check(TokenType.RIGHT_PAREN)) {
                break;
            }
            String name = this.expect(TokenType.IDENTIFIER).getText();
            parameters.add(new Parameter(name));
            if (!this.check(TokenType.COMMA)) {
                break;
            }
            this.nextToken();
            continue;
        }

        return parameters;
    }

    public Block parseBlock() {
        List<Statement> statements = new ArrayList<>();

        this.expect(TokenType.START_BLOCK);
        while (true) {
            if (this.check(TokenType.END_BLOCK)) {
                break;
            }
            statements.add(parseStatement());
        }
        this.expect(TokenType.END_BLOCK);

        return new Block(statements);
    }

    public AssignStatement parseAssigment() {
        String name = this.expect(TokenType.IDENTIFIER).getText();
        this.expect(TokenType.ASSIGN);
        Expression expression = this.parseExpression();

        return new AssignStatement(name, expression);
    }

    public Statement parseStatement() {
        switch (this.token.getType()) {
            case IDENTIFIER:
                Statement statement = this.parseAssigment();
                this.expect(TokenType.SEMICOLON);
                return statement;
            
            case START_BLOCK:
                return new BlockStatement(this.parseBlock());
            
            case IF:
                this.expect(TokenType.IF);
                this.expect(TokenType.LEFT_PAREN);
                Expression condition = this.parseExpression();
                this.expect(TokenType.RIGHT_PAREN);
                Statement thenStatement = this.parseStatement();
                this.expect(TokenType.ELSE);
                Statement elseStatement = this.parseStatement();

                return new IfStatement(condition, thenStatement, elseStatement);
            
            case PRINT:
                this.expect(TokenType.PRINT);
                Expression printExpr = this.parseExpression();
                this.expect(TokenType.SEMICOLON);

                return new PrintStatement(printExpr);
            
            case RETURN:
                this.expect(TokenType.RETURN);
                Expression returnExpr = this.parseExpression();
                this.expect(TokenType.SEMICOLON);

                return new ReturnStatement(returnExpr);

            case WHILE:
                this.expect(TokenType.WHILE);
                this.expect(TokenType.LEFT_PAREN);
                Expression loopCondition = this.parseExpression();
                this.expect(TokenType.RIGHT_PAREN);
                Statement loopBody = this.parseStatement();

                return new WhileStatement(loopCondition, loopBody);

            case FOR:
                this.expect(TokenType.FOR);
                this.expect(TokenType.LEFT_PAREN);
                Statement init = this.parseAssigment();
                this.expect(TokenType.SEMICOLON);
                Expression forCondition = this.parseExpression();
                this.expect(TokenType.SEMICOLON);
                Statement post = this.parseAssigment();
                this.expect(TokenType.RIGHT_PAREN);
                Statement forBody = this.parseStatement();

                return new BlockStatement(new Block(Arrays.asList(
                    init,
                    new WhileStatement(forCondition, new BlockStatement(new Block(Arrays.asList(
                        forBody,
                        post
                    ))))
                )));

            default:
                throw this.lexer.error(String.format("Statement expected at token %s", this.token));
        }
    }

    public Expression parseExpression() {
        return parseRelational();
    }

    // relational operators, e.g. <, >, ==, etc.
    public Expression parseRelational() {
        Expression lhs = this.parseNumerical();
        while (true) {
            if (this.check(TokenType.LESS_THAN)) {
                this.expect(TokenType.LESS_THAN);
                lhs = new OperatorExpression(Operator.LESS_THAN, lhs, this.parseNumerical());
            } else if (this.check(TokenType.EQUALS)) {
                this.expect(TokenType.EQUALS);
                lhs = new OperatorExpression(Operator.EQUALS, lhs, this.parseNumerical());
            } else {
                break;
            }
        }

        return lhs;
    }

    // numerical operators at the precedence of +
    public Expression parseNumerical() {
        Expression lhs = this.parseTerm();

        while (true) {
            if (this.check(TokenType.PLUS)) {
                this.expect(TokenType.PLUS);
                lhs = new OperatorExpression(Operator.ADD, lhs, this.parseTerm());
            } else if (this.check(TokenType.MINUS)) {
                this.expect(TokenType.MINUS);
                lhs = new OperatorExpression(Operator.SUBTRACT, lhs, this.parseTerm());
            } else {
                break;
            }
        }

        return lhs;
    }

    // numerical operators at the precedence of *
    // TODO: Implement division operator (TokenType.SLASH => Operator.DIVIDE)
    public Expression parseTerm() {
        Expression lhs = this.parseFactor();

        while (true) {
            if (this.check(TokenType.STAR)) {
                this.expect(TokenType.STAR);
                lhs = new OperatorExpression(Operator.MULTIPLY, lhs, this.parseFactor());
            } else if (this.check(TokenType.SLASH)) {
                this.expect(TokenType.SLASH);
                lhs = new OperatorExpression(Operator.DIVIDE, lhs, this.parseFactor());
            } else {
                break;
            }
        }

        return lhs;
    }

    // atomic expressions: literals, variables, calls and parenthesized expressions
    public Expression parseFactor() {
        if (this.check(TokenType.INTEGER_LITERAL)) {
            int value = Integer.parseInt(this.expect(TokenType.INTEGER_LITERAL).getText());
            return new ConstantExpression(value);
        } else if (this.check(TokenType.IDENTIFIER)) {
            String varName = this.expect(TokenType.IDENTIFIER).getText();
            if (this.check(TokenType.LEFT_PAREN)) {
                // left paren after identifier ==> function call
                this.expect(TokenType.LEFT_PAREN);
                List<Expression> arguments = this.parseArguments();
                this.expect(TokenType.RIGHT_PAREN);
                return new CallExpression(varName, arguments);
            } else {
                return new VariableExpression(varName);
            }
        } else if (this.check(TokenType.LEFT_PAREN)) {
            this.expect(TokenType.LEFT_PAREN);
            Expression parenthesizedExpr = this.parseExpression();
            this.expect(TokenType.RIGHT_PAREN);

            return parenthesizedExpr;
        } else {
            throw this.lexer.error("Unexpected factor character");
        }
    }

    public List<Expression> parseArguments() {
        List<Expression> arguments = new ArrayList<>();

        while (true) {
            if (this.check(TokenType.RIGHT_PAREN)) {
                break;
            }
            Expression argument = this.parseExpression();
            arguments.add(argument);
            if (!this.check(TokenType.COMMA)) {
                break;
            }
            this.nextToken();
            continue;
        }

        return arguments;
    }
}
