int flag = 0;
(new Thread(() -> flag = 1)).start();
(new Thread(() -> print(flag))).start();
