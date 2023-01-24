import java.util.stream.IntStream;

class Sum {
    public static void main(String[] args) {
        int N = 4;

        // Fifty billion
        long n = 50L * 1000L * 1000L * 1000L;

        // Initialize threads here. If you have N threads, each of them should run n / N ++ operations.

        long sum =
            IntStream.range(0, N)
            .parallel()
            .mapToLong(i -> {
                long chunkSize = n / N;

                long localSum = 0;
                for (long j = 0; j < chunkSize; j++) {
                    localSum++;
                }
                return localSum;
            })
            .sum();

        System.out.println(String.format("n   = %d", n));
        System.out.println(String.format("sum = %d", sum));
    }
}
