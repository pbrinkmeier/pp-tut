import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.awt.image.DataBufferByte;
import java.io.File;
import java.io.IOException;
import javax.imageio.ImageIO;

public class Histogram {
  private static String INPUT_PATH = "./schloss.jpg";

  public static void main(String[] args) throws IOException {
    BufferedImage image = Histogram.readGrayscaleImage(Histogram.INPUT_PATH);

    int histogram[] = new int[256];

    // retrieve underlying bytes
    byte imageData[] = ((DataBufferByte) image.getRaster().getDataBuffer()).getData();

    System.out.println(String.format("%dx%d = %d", image.getWidth(), image.getHeight(), image.getWidth() * image.getHeight()));
    System.out.println(String.format("Number of bytes: %d", imageData.length));

    long begin = System.nanoTime();

    // Thread initialization etc. goes here

    for (byte pixel: imageData) {
      histogram[Byte.toUnsignedInt(pixel)]++;
    }
    long end = System.nanoTime();

    // Thread joining etc. goes here

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
