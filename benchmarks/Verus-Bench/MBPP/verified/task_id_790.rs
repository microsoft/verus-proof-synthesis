use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether every even index contains even numbers of a given list.

    assert!(!is_even_at_even_index(&vec![3, 2, 1]));
    assert!(!is_even_at_even_index(&vec![1, 2, 3]));
    assert!(is_even_at_even_index(&vec![2, 1, 4]));
}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
    {
        if ((index % 2) != (arr[index] % 2)) {
            assert(((index as int) % 2) != (arr[index as int] % 2));
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
