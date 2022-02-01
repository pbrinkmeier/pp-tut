class MaxAbsCombinator {
    //@ requires left != Integer.MIN_VALUE;
    //@ requires right != Integer.MIN_VALUE;
    //@ ensures \result <= left || \result <= right;
    //@ ensures \result >= left && \result >= right;
    int combine(int left, int right) {
        return Math.max(Math.abs(left), Math.abs(right));
    }
}

new MaxAbsCombinator().combine(
    random.nextInt(),
    random.nextInt());
