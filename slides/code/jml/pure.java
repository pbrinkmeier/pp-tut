class ResizingArray<A> {
    private A[] elements;
    private int elementCount;
    /*@ pure @*/ public int getElementCount();

    //@ ensures getElementCount() ==
    //@         \old(getElementCount()) + 1;
    public void add(A element) { ... }
}
