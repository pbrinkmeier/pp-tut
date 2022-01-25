public class HappensBefore {
    public static boolean ping = false;
    public static final int maxRuns = 100;

    public static void main(String[] args) {
        Thread pingThread = new Thread(()-> {
            for(int i = 0; i < maxRuns; i++) {
                while(ping) {}
                ping = true;
                System.out.println("Ping - Round " + i);
            }
        });
        Thread pongThread = new Thread(()-> {
            for(int i = 0; i < maxRuns; i++) {
                while(!ping) {}
                ping = false;
                System.out.println("Pong - Round " + i);
            }
        });
        pingThread.start();
        pongThread.start();
    }
}
