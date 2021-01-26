class ResizingArray<A> {
    private A[] elements;
    private /*@ spec_public @*/ int elementCount;

    //@ ensures elementCount ==
    //@         \old(elementCount) + 1;
    public void add(A element) { ... }
}
