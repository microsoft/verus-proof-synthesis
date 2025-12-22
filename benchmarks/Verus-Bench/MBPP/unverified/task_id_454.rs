use vstd::prelude::*;

fn main() {}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut index = 0;
    while index < text.len() {
        if text[index] == 90 || text[index] == 122 {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
