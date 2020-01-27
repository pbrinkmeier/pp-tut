package dirwalker;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicLong;

public class Dirwalker {
    public static void main(String[] args) {
        if (args.length != 1) {
            System.err.println("Please pass exactly one argument");
            System.exit(1);
        }

        File root = new File(args[0]);
        if (!root.exists()) {
            System.err.println("Please pass an existing file");
            System.exit(1);
        }

        Dirwalker sizeFinder = new Dirwalker(root);
        System.out.println(String.format("%s is %s", root, Dirwalker.formatBytes(sizeFinder.run())));
    }

    ////////////////////////
    
    private final File root;

    public Dirwalker(File root) {
        this.root = root;
    }

    public long run() {
        return this.parallel(this.root);
    }

    private long recursive(File file) {
        long size = file.length();
        File[] children;

        if (!Files.isSymbolicLink(file.toPath()) && file.isDirectory() && (children = file.listFiles()) != null) {
            for (File child: file.listFiles()) {
                size += this.recursive(child);
            }
        }

        return size;
    }

    private long parallel(File file) {
        LinkedBlockingQueue<File> queue = new LinkedBlockingQueue<>();
        try {
            queue.put(file);
        } catch (InterruptedException e) { System.err.println("Couldn't put()"); e.printStackTrace(); }

        AtomicLong totalSize = new AtomicLong(0);
        Semaphore pendingItems = new Semaphore(1);

        ArrayList<Thread> threads = new ArrayList<>();
        for (int i = 0; i < Runtime.getRuntime().availableProcessors(); i++) {
            Thread t = new Thread(() -> {
                while (true) {
                    try {
                        pendingItems.acquire();

                        File currentFile = queue.take();
                        totalSize.getAndAdd(currentFile.length());

                        File[] children;
                        if (!Files.isSymbolicLink(currentFile.toPath()) && currentFile.isDirectory() && (children = currentFile.listFiles()) != null) {
                            for (File child: children) {
                                queue.put(child);
                                pendingItems.release();
                            }
                        }
                    } catch (InterruptedException e) {
                        /* Thread has been interrupted because all threads are waiting */
                        break;
                    }
                }
            });
            t.start();
            threads.add(t);
        }

        while (pendingItems.getQueueLength() != threads.size()) {
        }

        for (Thread t: threads) {
            t.interrupt();
        }

        for (Thread t: threads) {
            try {
                t.join();
            } catch (InterruptedException e) { System.err.println("Couldn't join()"); e.printStackTrace(); }
        }

        return totalSize.get();
    }

    ////////////////////////

    private static String formatBytes(long size) {
        final String[] units = { "Ki", "Mi", "Gi", "Ti" };
        String prefix = "";
        float capped = (float) size;

        for (int i = units.length - 1; i >= 0; i--) {
            if (Math.pow(1024, i + 1) <= size) {
                prefix = units[i];
                capped = ((float) size) / ((float) Math.pow(1024, i + 1));
                break;
            }
        }

        return String.format(String.format("%.1f %sB", capped, prefix));
    }
}
