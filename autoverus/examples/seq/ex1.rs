## `Seq` Usage

1. Basic Structure and Properties:
    - Seq<A> has a length (len) and values at each index (index or [] operator).
    - The structure uses marker::PhantomData<A> to hold the type without storing actual data.

2. Construction Methods:
    - Empty Sequence: Seq::empty creates an empty sequence.
    - New Sequence: Seq::new(len, f) creates a sequence of specified length initialized with a function mapping indices to values.
    - Macro: seq! macro allows creating small sequences similar to std::vec!.

3. Manipulation Methods:
    - Push: Seq::push appends a value to the end of the sequence.
    - Update: Seq::update replaces the value at a specified index, leaving others unchanged.
    - Add: Seq::add concatenates two sequences.
    - Subrange: Seq::subrange creates a subsequence from a specified range.
    - Take: Seq::take returns the first n elements of the sequence.
    - Skip: Seq::skip returns the sequence excluding the first n elements.

4. Access Methods:
    - Length: Seq::len returns the length of the sequence.
    - Index: Seq::index returns the value at a given index, with a requirement to be within bounds.
    - First Element: Seq::first returns the first element.
    - Last Element: Seq::last returns the last element.

5. Equality and Comparison:
    - Extensional Equality: The operator =~= is used to prove two sequences are equal.
    - Deep Equality: The operator =~~= is for deep equality checks.

## Example Usage

1. Basic Structure and Properties:
```use vstd::seq::*;
use vstd::seq_lib::*;

proof fn test_seq() {
    let s1 = Seq::new(5, |i: int| 10 * i);
    assert(s1.len() == 5);
    assert(s1.index(3) == 30);
    let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
    assert(s1 =~= s2);
    assert(s1 === s2);
}
```
2. Construction Methods:
    - Empty Sequence:
        ```
        let empty_seq = Seq::<int>::empty();
        assert(empty_seq.len() == 0);
        ```
    - New Sequence:
        ```
        let s1 = Seq::new(5, |i: int| 10 * i);
        assert(s1.len() == 5);
        assert(s1.index(3) == 30);
        ```
    - Macro:
        ```
        let seq_macro = seq![10, 20, 30, 40];
        assert(seq_macro.len() == 4);
        assert(seq_macro.index(2) == 30);
        ```
3. Manipulation Methods:
    - Push:
        ```
        let mut seq_push = Seq::<int>::empty();
        seq_push = seq_push.push(10);
        seq_push = seq_push.push(20);
        assert(seq_push.len() == 2);
        assert(seq_push.index(1) == 20);
        ```
    - Update:
        ```
        let mut seq_update = Seq::new(3, |i: int| 10 * i);
        seq_update = seq_update.update(1, 25);
        assert(seq_update.index(1) == 25);
        ```
    - Add:
        ```
        let seq1 = Seq::new(3, |i: int| 10 * i);
        let seq2 = Seq::new(2, |i: int| 20 * i);
        let seq_add = seq1.add(seq2);
        assert(seq_add.len() == 5);
        assert(seq_add.index(3) == 0); // Value from seq2
        ```
    - Subrange:
        ```
        let seq_subrange = Seq::new(5, |i: int| 10 * i).subrange(1, 3);
        assert(seq_subrange.len() == 2);
        assert(seq_subrange.index(0) == 10);
        assert(seq_subrange.index(1) == 20);
        ```
    - Take:
        ```
        let seq_take = Seq::new(5, |i: int| 10 * i).take(3);
        assert(seq_take.len() == 3);
        assert(seq_take.index(2) == 20);
        ```
    - Skip:
        ```
        let seq_skip = Seq::new(5, |i: int| 10 * i).skip(2);
        assert(seq_skip.len() == 3);
        assert(seq_skip.index(0) == 20);
        ```
4. Access Methods:
    - Length:
        ```
        let seq_len = Seq::new(4, |i: int| 5 * i);
        assert(seq_len.len() == 4);
        ```
    - Index:
        ```
        let seq_index = Seq::new(4, |i: int| 5 * i);
        assert(seq_index.index(2) == 10);
        ```
    - First Element:
        ```
        let seq_first = Seq::new(4, |i: int| 5 * i);
        assert(seq_first.first() == 0);
        ```
    - Last Element:
        ```
        let seq_last = Seq::new(4, |i: int| 5 * i);
        assert(seq_last.last() == 15);
        ```
5. Equality and Comparison:
    - Extensional Equality:
        ```
        let s1 = Seq::new(5, |i: int| 10 * i);
        let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
        assert(s1 =~= s2);
        ```
    - Deep Equality:
        ```
        let s1 = Seq::new(5, |i: int| 10 * i);
        let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
        assert(s1 === s2);
        ```
