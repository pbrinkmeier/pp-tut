import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

class SumFutures {
    public static void main(String[] args) throws ExecutionException, InterruptedException {
        int N = 4;

        // Fifty billion
        long n = 50L * 1000L * 1000L * 1000L;

        // Initialize threads here. If you have N threads, each of them should run n / N ++ operations.
        ExecutorService executor = Executors.newFixedThreadPool(N);

        List<Future<Long>> futures = new ArrayList<>();

        for (int i = 0; i < N; i++) {
            futures.add(executor.submit(() -> {
                long chunkSize = n / N;
                long localSum = 0;
                for (long j = 0; j < chunkSize; j++) {
                    localSum++;
                }
                return localSum;
            }));
        }

        long sum = 0;
        for (Future<Long> future: futures) {
            sum += future.get();
        }

        executor.shutdown();

        System.out.println(String.format("n   = %d", n));
        System.out.println(String.format("sum = %d", sum));
    }
}
