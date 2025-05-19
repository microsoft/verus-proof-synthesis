use vstd::prelude::*;

fn main() {
    // Write a function in Rust that matches a word containing 'z'.

    assert!(contains_z(&("pythonz.".chars().collect())));
    assert!(contains_z(&("xyz.".chars().collect())));
    assert!(!contains_z(&("  lang  .".chars().collect())));
}

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|k: int| 0 <= k < index ==> (text[k] != 'Z' && text[k] != 'z'),
        decreases
            text.len() - index,
    {
        if text[index] == 'Z' || text[index] == 'z' {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
