Runnable r = ...; (new Thread(r)).start();
// Runnable is ein functional interface:
Thread t = new Thread(() -> {
  calculate999999thPrime();
});
t.start();
t.join();
