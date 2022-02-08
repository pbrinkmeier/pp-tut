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
    
    private List elements = new ArrayList<>();

    //@ ensures \result >= 0;
    /*@ pure @*/ public int size() {
        return elements.size();
    }

    //@ ensures size() == 0 <==> \result;
    /*@ pure @*/ public boolean isEmpty() {
        return size() == 0;
    }

    //@ ensures \old(getElements()).contains(element) ==> size() == \old(size());
    public void add(T element) {
        if (contains(element)) return;
        elements.add(element);
        // Da sollte es eigentlich eine Methode geben, die neue Elemente nur dann hinzufügt, wenn sie bereits in der Liste nicht vorkommen
    }

    // @ ensures getElements().contains(element) ==> \result;
    /*@ pure @*/ public boolean contains(T element) {
        return elements.contains(element);
    }

    //@ ensures \forall int i; i >= 0 && i < \result.size(); contains(\result.get(i));
    /*@ pure @*/ public List<T> getElements() {
        return elements;
    }
} 