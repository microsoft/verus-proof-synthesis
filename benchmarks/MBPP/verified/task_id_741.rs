use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check whether all the characters are same or not.

    assert!(!all_characters_same(&("python".chars().collect())));
    assert!(all_characters_same(&("aaa".chars().collect())));
    assert!(!all_characters_same(&("data".chars().collect())));
}

verus! {

fn all_characters_same(char_arr: &Vec<char>) -> (result: bool)
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
{
    if char_arr.len() <= 1 {
        return true;
    }
    let mut index = 1;
    while index < char_arr.len()
        invariant
            1 <= index <= char_arr.len(),
            forall|k: int| 0 <= k < index ==> char_arr[0] == #[trigger] char_arr[k],
        decreases
            char_arr.len() - index,
    {
        if char_arr[0] != char_arr[index] {
            assert(exists|i: int|
                1 <= i < char_arr@.len() && char_arr[0] != #[trigger] char_arr[i]);
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
