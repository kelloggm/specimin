package com.example;

class Foo {

    private enum Status {

        ON(1);

        int bitRep;

        Status(int x) {
            throw new Error();
        }
    }

    private void bar() {
        int y = Status.ON.bitRep;
    }
}
