@FunctionalInterface
interface PixelTransformation {
  int transform(int input);
}

PixelTransformation bw =
  x -> x < 128 ? 0 : 255;
