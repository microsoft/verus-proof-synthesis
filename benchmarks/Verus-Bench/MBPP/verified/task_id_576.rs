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
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= idx <= (main.len() - sub.len()),
            0 <= i <= sub.len(),
            0 <= idx + i <= main.len(),
            forall|k: int| 0 <= k < i ==> main[idx + k] == sub[k],
            forall|k: int|
                0 <= k < i ==> (main@.subrange(idx as int, (idx + k)) =~= sub@.subrange(0, k)),
    {
        if (main[idx + i] != sub[i]) {
            assert(exists|k: int| 0 <= k < i ==> main[idx + k] != sub[k]);
            assert(main@.subrange(idx as int, (idx + sub@.len())) != sub@);
            return false;

        }
        i += 1;
    }
    assert(main@.subrange(idx as int, (idx + sub@.len())) == sub@);
    true
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            sub.len() <= main.len(),
            0 <= index <= (main.len() - sub.len()) + 1,
            forall|k: int, l: int|
                (0 <= k < index) && l == k + sub.len() ==> (#[trigger] (main@.subrange(k, l))
                    != sub@),
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
