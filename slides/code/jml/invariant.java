class FixedSizeList<A> {
    //@ invariant elementCount <= elements.length;
    A[] elements;
    int elementCount;
}
