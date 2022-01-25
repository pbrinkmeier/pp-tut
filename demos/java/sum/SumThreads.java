import java.util.stream.IntStream;

class SumThreads {
    public static void main(String[] args) throws InterruptedException {
        int N = 4;

        // Fifty billion
        long n = 50L * 1000L * 1000L * 1000L;

        // Initialize threads here. If you have N threads, each of them should run n / N ++ operations.
        Thread threads[] = new Thread[N];
        long sums[] = new long[N];

        IntStream.range(0, N).forEach((i) -> {
            long chunkSize = n / N;
            Thread t = new Thread(() -> {
                long localSum = 0;
                for (long j = 0; j < chunkSize; j++) {
                    localSum++;
                }
                sums[i] = localSum;
            });
            threads[i] = t;
            t.start();
        });

        long sum = 0;
        for (int i = 0; i < N; i++) {
            threads[i].join();
            sum += sums[i];
        }

        System.out.println(String.format("n   = %d", n));
        System.out.println(String.format("sum = %d", sum));
    }
}
