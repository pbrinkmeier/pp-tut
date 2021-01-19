Function<Float, Float> f =
  new Function<Float, Float>() {
    @Override
    public Float apply(Float x) {
      return 2 * x;
    }
  };
Float tau = f.apply(pi);
