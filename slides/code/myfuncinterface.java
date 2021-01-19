@FunctionalInterface
interface PixelTransformation {
  byte transform(byte input);
}

PixelTransformation bw =
  x -> x < 128 ? 0 : 255;
