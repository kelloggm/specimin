package com.example;

import java.util.List;
import java.util.Collection;
import java.util.Iterator;
import java.util.ListIterator;

public class Baz<E> implements List<E> {

    public int size() {
        throw new Error();
    }

    public boolean isEmpty() {
        throw new Error();
    }

    public boolean contains(Object o) {
        throw new Error();
    }

    public Iterator<E> iterator() {
        throw new Error();
    }

    public Object[] toArray() {
        throw new Error();
    }

    public <T> T[] toArray(T[] a) {
        throw new Error();
    }

    public boolean add(E e) {
        throw new Error();
    }

    public boolean remove(Object o) {
        throw new Error();
    }

    public boolean containsAll(Collection<?> c) {
        throw new Error();
    }

    public boolean addAll(Collection<? extends E> c) {
        throw new Error();
    }

    public boolean addAll(int index, Collection<? extends E> c) {
        throw new Error();
    }

    public boolean removeAll(Collection<?> c) {
        throw new Error();
    }

    public boolean retainAll(Collection<?> c) {
        throw new Error();
    }

    public void clear() {
        throw new Error();
    }

    public E get(int index) {
        throw new Error();
    }

    public E set(int index, E element) {
        throw new Error();
    }

    public void add(int index, E element) {
        throw new Error();
    }

    public E remove(int index) {
        throw new Error();
    }

    public int indexOf(Object o) {
        throw new Error();
    }

    public int lastIndexOf(Object o) {
        throw new Error();
    }

    public ListIterator<E> listIterator() {
        throw new Error();
    }

    public ListIterator<E> listIterator(int index) {
        throw new Error();
    }

    public List<E> subList(int fromIndex, int toIndex) {
        throw new Error();
    }
}
