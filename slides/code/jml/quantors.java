/*@ requires \forall int i;
    0 <= i && i < xs.length;
    xs[i] != null;
    ensures xs.length == 0 ==> \result == 0;
  @*/
int totalLength(String[] xs) {
    ...
}
