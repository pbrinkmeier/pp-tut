package set;

import java.util.ArrayList;
import java.util.List;

public class Set<T> {
    public static void main(String[] args) {
        Set<String> s = new Set<>();
        s.add("abc");
        s.add("xyz");
        s.add("abc");
        
        for (String str: s.getElements()) {
            System.out.println(str);
        }
    }

    private List<T> elements = new ArrayList<>();

    //@ ensures \result >= 0;
    /*@ pure @*/ public int size() {
        return 0;
    }

    public boolean isEmpty() {
        return true;
    }

    public boolean add(T element) {
        return false;
    }

    public boolean contains(T element) {
        return false;
    }

    public List<T> getElements() {
        return elements;
    }
} 
