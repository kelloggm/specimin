package com.example;

public class Simple extends Foo {
    public static void bar() {
        Simple s = new Simple(5);
        Foo f = new Foo(5, null);
    }

    public Simple(int x) {
        super(x, null);
    }
}

