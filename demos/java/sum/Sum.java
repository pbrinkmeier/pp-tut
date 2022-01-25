class Sum {
    public static void main(String[] args) {
        // Fifty billion
        long n = 50L * 1000L * 1000L * 1000L;

        // Initialize threads here. If you have N threads, each of them should run n / N ++ operations.

        long sum = 0;
        for (long i = 0; i < n; i++) {
            sum++;
        }

        System.out.println(String.format("n   = %d", n));
        System.out.println(String.format("sum = %d", sum));
    }
}
