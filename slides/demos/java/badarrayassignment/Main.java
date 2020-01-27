import java.math.BigInteger;

class Main {
    int[] x = new int[10];
    Integer[] y = new Integer[10];
    BigInteger[] z = new BigInteger[10];

    //@ requires x.length >= 1;
    //@ requires y.length >= 1;
    //@ requires z.length >= 1;
    //  vvvvvvvv Wenn man diese Vorbedingung entfernt, erscheint eine PossiblyBadArrayException-warning (wieso?)
    //@ requires \typeof(z) == \type(BigInteger[]);
    void f() {
        int[] a = new int[10];
        Integer[] b = new Integer[10];
        BigInteger[] c = new BigInteger[10];

        a[0] = 42;
        b[0] = 42;
        c[0] = new BigInteger("42");

        x[0] = 42;
        y[0] = 42;
        z[0] = new BigInteger("42");
    }
}
