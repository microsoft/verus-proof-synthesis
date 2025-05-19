use vstd::prelude::*;

fn main() {
    // Write a function in Rust to convert a given string to uppercase.

    assert_eq!(
        to_uppercase(&("person".chars().collect()))
            .iter()
            .collect::<String>(),
        "PERSON"
    );
    assert_eq!(
        to_uppercase(&("final".chars().collect()))
            .iter()
            .collect::<String>(),
        "FINAL"
    );
    assert_eq!(
        to_uppercase(&("Valid".chars().collect()))
            .iter()
            .collect::<String>(),
        "VALID"
    );
}

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
            0 <= index <= str1.len(),
            upper_case.len() == index,
            forall|i: int|
                0 <= i < index ==> (upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                    shift_minus_32_spec(str1[i])
                } else {
                    str1[i]
                })),
        decreases
            str1.len() - index,
    {
        if (str1[index] >= 'a' && str1[index] <= 'z') {
            upper_case.push(((str1[index] as u8) - 32) as char);
        } else {
            upper_case.push(str1[index]);
        }
        assert(upper_case[index as int] == (if is_lower_case(str1[index as int]) {
            shift_minus_32_spec(str1[index as int])
        } else {
            str1[index as int]
        }));
        index += 1;
    }
    assert(forall|i: int|
        0 <= i < str1.len() ==> upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
            shift_minus_32_spec(str1[i])
        } else {
            str1[i]
        }));
    upper_case
}

} // verus!
