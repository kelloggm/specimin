package com.example;

import java.util.List;

class Foo<E> extends Baz<E> implements List<E> {

    public void bar(E input) {
        this.add(input);
    }
}
