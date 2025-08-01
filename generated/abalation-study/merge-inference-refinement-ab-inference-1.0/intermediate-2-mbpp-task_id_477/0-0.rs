use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_upper_case(c: char) -> bool {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> char {
    ((c as u8) + 32) as char
}

fn to_lowercase(str1: &Vec<char>) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
{
    let mut lower_case: Vec<char> = Vec::with_capacity(str1.len());
    let mut index = 0;
    
    while index < str1.len()
        invariant
            index <= str1.len(),
            lower_case.len() == index,
            str1.len() == old(str1).len(), // Array length invariant
            forall|i: int|
                0 <= i < index ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
                    shift32_spec(str1[i])
                } else {
                    str1[i]
                }),
    {
        if (str1[index] >= 'A' && str1[index] <= 'Z') {
            lower_case.push(((str1[index] as u8) + 32) as char);
        } else {
            lower_case.push(str1[index]);
        }
        index += 1;
    }
    
    lower_case
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1