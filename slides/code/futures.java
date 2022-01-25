Executor e = Executor.newFixedThreadPool(N);

Future<Long> f = e.submit(() -> {
  return calculate999999thPrime();
});
long result = f.get();

e.shutdown();
