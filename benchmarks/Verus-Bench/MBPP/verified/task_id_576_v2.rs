/*This is a slightly simpler version of proof provided by Chris Hawblitzel*/
use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether a list is sublist of another or not.

    assert!(!is_sub_array(&vec![1, 4, 3, 5], &vec![1, 2]));
    assert!(is_sub_array(&vec![1, 2, 1], &vec![1, 2, 1]));
    assert!(!is_sub_array(&vec![1, 0, 2, 2], &vec![2, 2, 0]));
    assert!(is_sub_array(&vec![1, 0, 2, 2], &vec![2, 2]));
    assert!(is_sub_array(&vec![1, 0, 2, 2], &vec![1, 0]));

    assert_eq!(
        sub_array_at_index(&vec![1, 0, 2, 2], &vec![1, 0, 2, 2], 0),
        true
    );
    assert_eq!(
        sub_array_at_index(&vec![1, 0, 2, 2], &vec![1, 0, 2, 2], 1),
        false
    );
}

verus! {

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
    {
        if (main[idx + i] != sub[i]) {
            return false;

        }
        i += 1;
    }
    true
}

spec fn is_subrange_at(main: Seq<i32>, sub: Seq<i32>, i: int) -> bool {
    sub =~= main.subrange(i, i + sub.len())
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|k: int|
            0 <= k <= (main.len() - sub.len()) && is_subrange_at(main@, sub@, k)),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            sub.len() <= main.len(),
            0 <= index <= (main.len() - sub.len()) + 1,
            forall|k: int| 0 <= k < index ==> !is_subrange_at(main@, sub@, k),
    {
        if (sub_array_at_index(&main, &sub, index)) {
            assert(is_subrange_at(main@, sub@, index as int));
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
