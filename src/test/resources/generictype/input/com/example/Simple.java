package com.example;

import org.test.MyBinaryTree;
import java.util.Map;

public class Simple<T> {
    private Map<MyBinaryTree, Integer> tree;
    private T content;
    public Simple(T content) {
        this.content = content;
    }
}

