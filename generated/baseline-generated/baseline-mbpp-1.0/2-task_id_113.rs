use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_digit_spec(c: char) -> bool {
    (c as u32) >= 48 && (c as u32) <= 57
}

fn is_digit(c: char) -> (res: bool)
    ensures
        res == is_digit_spec(c),
{
    (c as u32) >= 48 && (c as u32) <= 57
}

fn is_integer(text: &Vec<char>) -> (result: bool)
    ensures
        result == (forall |i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_spec(text[i]))),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall |i: int| 0 <= i < index ==> is_digit_spec(text[i]),
    {
        if !is_digit(text[index]) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: (3, 0)
// Safe: False