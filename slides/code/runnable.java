Runnable r = ...; (new Thread(r)).start();
// Runnable ist ein functional interface:
Thread t = new Thread(() -> {
  calculate999999thPrime();
});
t.start();
t.join();
