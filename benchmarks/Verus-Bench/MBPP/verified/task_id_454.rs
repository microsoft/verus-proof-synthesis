use vstd::prelude::*;

fn main() {
    // Write a function in Rust that matches a word containing 'z'.

    assert!(contains_z(b"pythonz."));
    assert!(contains_z(b"xyz."));
    assert!(!contains_z(b"  lang  ."));
}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|k: int| 0 <= k < index ==> (text[k] != 90 && text[k] != 122),
    {
        if text[index] == 90 || text[index] == 122 {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
