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
    while index < char_arr.len() {
        if char_arr[0] != char_arr[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
