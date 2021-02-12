package set;

import java.util.ArrayList;
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

    private List<T> elements;

    public Set() {
        elements = new ArrayList<>();
    }

    //@ ensures isEmpty() ==> \result == 0;
    /*@ pure @*/ public int size() {
        return elements.size();
    }

    //@ ensures size() == 0 ==> \result;
    /*@ pure @*/ public boolean isEmpty() {
        return size() == 0;
    }

    //@ ensures \old(getElements()).contains(element) ==> size() == \old(size());
    public void add(T element) {
      if (!elements.contains(element)) {
        elements.add(element);
      }
    }

    /*@ pure @*/ public boolean contains(T element) {
        return elements.contains(element);
    }

    /*@ pure @*/ public List<T> getElements() {
        return this.elements;
    }
}
