import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.awt.image.DataBufferByte;
import java.io.File;
import java.io.IOException;
import java.util.stream.IntStream;
import javax.imageio.ImageIO;

public class HistogramT {
  private static String INPUT_PATH = "./schloss.jpg";

  public static void main(String[] args) throws IOException {
    BufferedImage image = HistogramT.readGrayscaleImage(HistogramT.INPUT_PATH);

    int histogram[] = new int[256];

    // retrieve underlying bytes
    byte imageData[] = ((DataBufferByte) image.getRaster().getDataBuffer()).getData();

    System.out.println(String.format("%dx%d = %d", image.getWidth(), image.getHeight(), image.getWidth() * image.getHeight()));
    System.out.println(String.format("Number of bytes: %d", imageData.length));

    // Thread initialization etc. goes here
    
    int nThreads = 4;
    int histograms[][] = new int[nThreads][];
    Thread threads[] = new Thread[nThreads];

    int blockSize = imageData.length / nThreads;

    long begin = System.nanoTime();

    IntStream.range(0, nThreads).forEach(i -> {
      histograms[i] = new int[256];
      threads[i] = new Thread(() -> {
        for (int k = 0; k < blockSize; k++) {
          byte pixel = imageData[i * blockSize + k];
          histograms[i][Byte.toUnsignedInt(pixel)]++;
        }
      });
      threads[i].start();
    });

    IntStream.range(0, nThreads).forEach(i -> {
      try {
        threads[i].join();
        for (int k = 0; k < 256; k++) {
          histogram[k] += histograms[i][k];
        }
      } catch (InterruptedException e) {
        // ignored
      }
    });

    long end = System.nanoTime();

    for (int i = 0; i < 256; i++) {
      System.out.println(String.format("#%03d = %8d", i, histogram[i]));
    }

    System.out.println(String.format("I took %d nanoseconds for %d pixels", end - begin, imageData.length));
  }

  // ---
  
  private static BufferedImage readGrayscaleImage(String path) throws IOException {
    BufferedImage original = ImageIO.read(new File(path));
    BufferedImage grayscale = new BufferedImage(original.getWidth(), original.getHeight(), BufferedImage.TYPE_BYTE_GRAY);
    Graphics g = grayscale.getGraphics();
    g.drawImage(original, 0, 0, null);
    g.dispose();
    return grayscale;
  }
}
