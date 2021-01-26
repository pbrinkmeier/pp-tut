package set;

import java.util.List;

public class Set<T> {
    public static void main(String[] args) {
        Set<Integer> s = new Set<>();
        s.add(42);
        s.add(100);
        s.add(42);
        for (Integer i: s.getElements()) {
            System.out.println(String.format("%d", i));
        }
    }

    public int size() {
        return -1;
    }

    //@ ensures size() == 0 ==> \result;
    public boolean isEmpty() {
        return false;
    }

    //@ ensures \old(getElements()).contains(element) ==> size() == \old(size());
    public void add(T element) {
    }

    public boolean contains(T element) {
        return false;
    }

    public List<T> getElements() {
        return null;
    }
}
