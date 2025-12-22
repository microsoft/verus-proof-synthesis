use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find whether all the given list of sequences have equal length or not.

    assert!(all_sequence_equal_length(
        &(vec![vec![11, 22, 33], vec![44, 55, 66]])
    ));
    assert!(!all_sequence_equal_length(
        &(vec![vec![1, 2, 3], vec![4, 5, 6, 7]])
    ));
    assert!(all_sequence_equal_length(&(vec![vec![1, 2], vec![3, 4]])));
}

verus! {

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    let mut index = 1;
    while index < seq.len()
        invariant
            1 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
    {
        if ((&seq[index]).len() != (&seq[0]).len()) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
