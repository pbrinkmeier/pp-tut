func main() {
    x = 17 + 25;
    bound = 100;

    if (x < bound)
        print x;
    else {
        print bound;
        y = 0;
    }

    print twice(bound);
    print factorial(10);

    i = 0;
    while (i < 10) {
        print i;
        i = i + 1;
    }
}

func twice(x) {
    return x + x;
}

func factorial(n) {
    if (n == 0) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
}
