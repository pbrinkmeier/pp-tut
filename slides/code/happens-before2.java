int flag = 0;
(new Thread(() -> {
  while (!flag) {}
  print("Active!");
})).start();
Thread.sleep(1000);
flag = 1;
