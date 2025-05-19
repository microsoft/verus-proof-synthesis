use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check if a string represents an integer or not.

    assert!(!is_integer(&("python".chars().collect())));
    assert!(is_integer(&("1".chars().collect())));
    assert!(is_integer(&("123".chars().collect())));
}

verus! {

spec fn is_digit_sepc(c: char) -> bool {
    (c as u32) >= 48 && (c as u32) <= 57
}

fn is_digit(c: char) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    (c as u32) >= 48 && (c as u32) <= 57
}

fn is_integer(text: &Vec<char>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|i: int| 0 <= i < index ==> (#[trigger] is_digit_sepc(text[i])),
        decreases
            text.len() - index,
    {
        if (!is_digit(text[index])) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
