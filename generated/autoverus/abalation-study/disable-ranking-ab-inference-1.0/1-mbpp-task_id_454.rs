use vstd::prelude::*;
fn main() {}
verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    let mut index = 0;
    while index < text.len()
        invariant
            exists|i: int|
                0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z') ==> exists|i: int|
                    0 <= i < index && (text[i] == 'Z' || text[i] == 'z'),
            forall|i: int| 0 <= i < index ==> text[i] != 'Z' && text[i] != 'z',
            index <= text.len(),
    {
        if text[index] == 'Z' || text[index] == 'z' {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!


// Score: (1, 1)
// Safe: True