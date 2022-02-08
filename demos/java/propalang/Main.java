import ast.*;
import parser.*;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Collectors;

class Main {
    public static void main(String[] args) {
        System.out.println("Hello, propalang!");

        String command = args.length < 2 ? "test" : args[1];

        switch (command) {
            case "test":
                test();
                break;
            case "lex":
                lex(args[2]);
                break;
            case "run":
                run(args[2]);
                break;
        }
    }

    public static void test() {
        Program testProgram = new Program(Arrays.asList(
            new Func("main", Arrays.asList(), new Block(Arrays.asList(
                new AssignStatement("x", new OperatorExpression(Operator.ADD, new ConstantExpression(17), new ConstantExpression(25))),
                new AssignStatement("bound", new ConstantExpression(100)),
                new IfStatement(
                    new OperatorExpression(Operator.LESS_THAN, new VariableExpression("x"), new VariableExpression("bound")),
                    new PrintStatement(new VariableExpression("x")),
                    new BlockStatement(new Block(Arrays.asList(
                        new PrintStatement(new VariableExpression("bound")),
                        new AssignStatement("y", new ConstantExpression(0))
                    )))
                ),
                new PrintStatement(new CallExpression("twice", Arrays.asList(new VariableExpression("bound")))),
                new PrintStatement(new CallExpression("factorial", Arrays.asList(new ConstantExpression(10)))),
                new AssignStatement("i", new ConstantExpression(0)),
                new WhileStatement(
                    new OperatorExpression(Operator.LESS_THAN, new VariableExpression("i"), new ConstantExpression(10)),
                    new BlockStatement(new Block(Arrays.asList(
                        new PrintStatement(new VariableExpression("i")),
                        new AssignStatement("i", new OperatorExpression(Operator.ADD, new VariableExpression("i"), new ConstantExpression(1)))
                    )))
                )
            ))),
            new Func("twice", Arrays.asList(new Parameter("x")), new Block(Arrays.asList(
                new ReturnStatement(new OperatorExpression(Operator.ADD, new VariableExpression("x"), new VariableExpression("x")))
            ))),
            new Func("factorial", Arrays.asList(new Parameter("n")), new Block(Arrays.asList(
                new IfStatement(
                    new OperatorExpression(Operator.EQUALS, new VariableExpression("n"), new ConstantExpression(0)),
                    new ReturnStatement(new ConstantExpression(1)),
                    new ReturnStatement(new OperatorExpression(
                        Operator.MULTIPLY,
                        new VariableExpression("n"),
                        new CallExpression("factorial", Arrays.asList(
                            new OperatorExpression(Operator.SUBTRACT, new VariableExpression("n"), new ConstantExpression(1))
                        ))
                    ))
                )
            )))
        ));

        testProgram.run();
    }

    public static void lex(String fileName) {
        PropaLangLexer lexer = new PropaLangLexer(readFile(fileName));

        Token t;
        while ((t = lexer.lex()).getType() != TokenType.EOF) {
            System.out.println(t);
        }
    }

    public static void run(String fileName) {
        PropaLangParser parser = new PropaLangParser(readFile(fileName));
        Program p = parser.parseProgram();
        p.run();
    }

    public static String readFile(String fileName) {
        try {
            return Files.lines(Paths.get(fileName), StandardCharsets.UTF_8).collect(Collectors.joining("\n"));
        } catch (IOException e) {
            throw new RuntimeException(String.format("Could not read file %s", fileName));
        }
    }
}
