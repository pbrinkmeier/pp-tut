import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.awt.image.DataBufferByte;
import java.io.File;
import java.io.IOException;
import java.util.stream.IntStream;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import javax.imageio.ImageIO;

public class HistogramE {
  private static String INPUT_PATH = "./schloss.jpg";

  public static void main(String[] args) throws IOException {
    BufferedImage image = HistogramE.readGrayscaleImage(HistogramE.INPUT_PATH);

    int histogram[] = new int[256];

    // retrieve underlying bytes
    byte imageData[] = ((DataBufferByte) image.getRaster().getDataBuffer()).getData();

    System.out.println(String.format("%dx%d = %d", image.getWidth(), image.getHeight(), image.getWidth() * image.getHeight()));
    System.out.println(String.format("Number of bytes: %d", imageData.length));

    int nThreads = 2;
    Future futures[] = new Future[nThreads];
    int histograms[][] = new int[nThreads][];
    ExecutorService executor = Executors.newFixedThreadPool(nThreads);

    int blockSize = imageData.length / nThreads;

    long begin = System.nanoTime();

    IntStream.range(0, nThreads).forEach(i -> {
      histograms[i] = new int[256];
      futures[i] = executor.submit(() -> {
        for (int k = 0; k < blockSize; k++) {
          byte pixel = imageData[i * blockSize + k];
          histograms[i][Byte.toUnsignedInt(pixel)]++;
        }
      });
    });

    IntStream.range(0, nThreads).forEach(i -> {
      try {
        futures[i].get();
      } catch (InterruptedException e) {
      } catch (ExecutionException e) {
      }
      for (int k = 0; k < 256; k++) {
        histogram[k] += histograms[i][k];
      }
    });

    executor.shutdown();

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
