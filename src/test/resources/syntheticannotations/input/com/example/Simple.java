package com.example;

public class Simple {
    @Bar(10)
    @Baz(foo = "foo", bar = 1)
    public static int baz(String bar) {
        return 1;
    }
}
