package rpncalculator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

class RpnCalculator {
    public static void main(String[] args) {
        if (args.length != 1) {
            System.err.println("Please pass exactly 1 argument");
            System.exit(1);
        }

        List<Token> program = RpnCalculator.tokenize(args[0]);
        // Print out tokens for debugging
        System.err.println(String.format("[%s]", String.join(", ", program.stream().map(Token::toString).collect(Collectors.toList()))));
        RpnCalculator calculator = new RpnCalculator();
        calculator.execute(program);
        calculator.printStack();
    }

    ///////////////
    
    private final static int MIN_SIZE = 10;

    private /*@ spec_public @*/ BigInteger[] stack;
    private int elementCount;
    
    public RpnCalculator() {
        this.stack = new BigInteger[RpnCalculator.MIN_SIZE];
        this.elementCount = 0;
    }

    public void execute(List<Token> program) {
        for (Token t: program) {
            switch (t.getType()) {
                case NUMBER:
                    this.push(new BigInteger(t.text));
                    break;
                case ADD:
                    this.push(this.pop().add(this.pop()));
                    break;
                case IDENTIFIER:
                    this.handleIdentifier(t.getText());
                    break;
                case WHITESPACE:
                    // ignore
                    break;
                default:
                    System.err.println(String.format("I don't know what to do with %s", t));
                    System.exit(1);
                    break;
            }
        }
    }

    //@ ensures id.equals("gcd") ==> stack[stack.length - 1] == euclideanGcd(\old(stack[stack.length - 1]), \old(stack[stack.length - 2]));
    public void handleIdentifier(String id) {
        // greatest common divisor
        if (id.equals("gcd")) {
            this.push(RpnCalculator.euclideanGcd(this.pop(), this.pop()));
        } else if (id.equals("fac")) {
            this.push(RpnCalculator.factorial(this.pop()));
        } else {
            System.err.println(String.format("%s is not defined", id));
            System.exit(1);
        }
    }

    ///////// some algorithms

    private /*@ spec_public pure @*/ static BigInteger euclideanGcd(BigInteger a, BigInteger b) {
        BigInteger smol = a.min(b);
        BigInteger bigg = a.max(b);

        // avoid infinite loop
        if (smol.compareTo(BigInteger.ZERO) < 0) {
            System.err.println(String.format("GCD of %s and %s is not defined", smol, bigg));
            System.exit(1);
        }

        while (!smol.equals(BigInteger.ZERO)) {
            BigInteger tmp = bigg.mod(smol);
            bigg = smol;
            smol = tmp;
        }

        return bigg;
    }

    private static BigInteger factorial(BigInteger n) {
        if (n.compareTo(BigInteger.ZERO) < 0) {
            System.err.println(String.format("Factorial of %s is not defined", n));
            System.exit(1);
        }

        BigInteger fac = BigInteger.ONE;
        for (; !n.equals(BigInteger.ZERO); n = n.subtract(BigInteger.ONE)) {
            fac = fac.multiply(n);
        }

        return fac;
    }

    /////////// Internals

    /*@ pure @*/
    public void printStack() {
        String repr = "[";
        for (int i = 0; i < this.elementCount; i++) {
            repr += this.stack[i].toString();
            if (i != this.elementCount - 1) {
                repr += ", ";
            }
        }
        repr += "]";

        System.out.println(String.format("%s, %d/%d slots used", repr, this.elementCount, this.stack.length));
    }

    //@ requires \typeof(x) == \typeof(BigInteger.ZERO);
    private void push(BigInteger x) {
        if (this.stack.length == this.elementCount) {
            // Double array size
            BigInteger[] newStack = new BigInteger[this.elementCount * 2];
            System.arraycopy(this.stack, 0, newStack, 0, this.elementCount);
            this.stack = newStack;
        }

        this.stack[this.elementCount++] = x;
    }

    //@ requires elementCount <= stack.length;
    //@ requires elementCount > 0 ==> stack[elementCount] != null;
    //@ ensures  elementCount > 0 ==> elementCount == \old(elementCount) - 1;
    private BigInteger pop() {
        if (this.elementCount <= 0) {
            System.err.println("Could not pop");
            System.exit(1);
        }

        BigInteger x = this.stack[--this.elementCount];

        if (this.stack.length > RpnCalculator.MIN_SIZE && this.elementCount == this.stack.length / 2) {
            // Halve array size
            BigInteger[] newStack = new BigInteger[this.elementCount];
            System.arraycopy(this.stack, 0, newStack, 0, this.elementCount);
            this.stack = newStack;
        }

        return x;
    }

    ///////////////
    
    private enum TokenType {
        WHITESPACE,
        NUMBER,
        ADD,
        SUBTRACT,
        MULTIPLY,
        DIVIDE,
        IDENTIFIER
    }
    
    private static class Token {
        private final TokenType type;
        private final String text;

        public Token(TokenType type, String text) {
            this.type = type;
            this.text = text;
        }

        public TokenType getType() { return this.type; }
        public String getText() { return this.text; }

        public String toString() {
            return String.format("%s[%s]", this.getType(), this.getText());
        }
    }
    
    private static List<Token> tokenize(String source) {
        // Inefficient and bad, not important right now
        List<Token> tokens = new ArrayList<Token>();

        while (!source.equals("")) {
            int pos = 0;
            TokenType t = null;
            if (Character.isWhitespace(source.charAt(0))) {
                while (pos < source.length() && Character.isWhitespace(source.charAt(pos))) {
                    pos++;
                }
                t = TokenType.WHITESPACE;
            } else if (Character.isDigit(source.charAt(0))) {
                while (pos < source.length() && Character.isDigit(source.charAt(pos))) {
                    pos++;
                }
                t = TokenType.NUMBER;
            } else if (source.charAt(0) == '+') {
                pos = 1;
                t = TokenType.ADD;
            } else if (source.charAt(0) == '-') {
                pos = 1;
                t = TokenType.SUBTRACT;
            } else if (source.charAt(0) == '*') {
                pos = 1;
                t = TokenType.MULTIPLY;
            } else if (source.charAt(0) == '/') {
                pos = 1;
                t = TokenType.DIVIDE;
            } else if (Character.isLetter(source.charAt(0))) {
                while (pos < source.length() && Character.isLetter(source.charAt(pos))) {
                    pos++;
                }
                t = TokenType.IDENTIFIER;
            } else {
                System.err.println(String.format("Parse error at: %s", source));
                System.exit(1);
            }

            tokens.add(new Token(t, source.substring(0, pos)));
            source = source.substring(pos, source.length());
        }

        return tokens;
    }
}
