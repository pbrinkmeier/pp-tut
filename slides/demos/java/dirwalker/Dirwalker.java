package dirwalker;

import java.io.File;

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
        return this.recursive(this.root);
    }

    private long recursive(File file) {
        long size = file.length();
        File[] children;

        if ((children = file.listFiles()) != null) {
            for (File child: file.listFiles()) {
                size += this.recursive(child);
            }
        }

        return size;
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
