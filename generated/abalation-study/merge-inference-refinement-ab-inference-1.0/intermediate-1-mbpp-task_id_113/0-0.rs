use vstd::prelude::*;

fn main() {}

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
            index <= text.len(),
            forall|i: int| 0 <= i < index ==> is_digit_sepc(text[i]),
            text.len() <= 100, // Assuming text length is bounded by a constant
    {
        if (!is_digit(text[index])) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1