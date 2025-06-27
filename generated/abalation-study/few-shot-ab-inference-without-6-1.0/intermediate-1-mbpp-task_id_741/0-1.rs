use vstd::prelude::*;

fn main() {}

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
            char_arr.len() > 1,
            forall|i: int| 1 <= i < index ==> char_arr[0] == char_arr[i],
    {
        if char_arr[0] != char_arr[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1