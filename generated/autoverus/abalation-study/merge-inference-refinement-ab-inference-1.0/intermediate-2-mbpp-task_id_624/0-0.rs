
use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_lower_case(c: char) -> bool {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> char {
    ((c as u8) - 32) as char
}

fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
{
    let mut upper_case: Vec<char> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            index <= str1.len(),
            upper_case.len() == index,
            forall|i: int| 0 <= i < index ==> (upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
            str1.len() == old(str1.len()),
    {
        if (str1[index] >= 'a' && str1[index] <= 'z') {
            upper_case.push(((str1[index] as u8) - 32) as char);
        } else {
            upper_case.push(str1[index]);
        }
        index += 1;
    }
    upper_case
}

}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1