package com.example;

import java.util.List;

// Suppose this is an isolated Java program from a real life project, and all of the implementation
// for methods from List are in Baz, then Specimin should simply remove List<E> from the class
// declaration.
class Foo<E> extends Baz<E> implements List<E> {
    public void bar(E input) {
        this.add(input);
    }

}
