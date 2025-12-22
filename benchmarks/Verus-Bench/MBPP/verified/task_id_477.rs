use vstd::prelude::*;

fn main() {
    // Write a function in Rust to convert the given string to lower case.

    assert_eq!(to_lowercase(b"InValid"), b"invalid");
    assert_eq!(to_lowercase(b"TruE"), b"true");
    assert_eq!(to_lowercase(b"SenTenCE"), b"sentence");
}

verus! {

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

fn to_lowercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
{
    let mut lower_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            lower_case.len() == index,
            forall|i: int|
                0 <= i < index ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
                    shift32_spec(str1[i])
                } else {
                    str1[i]
                }),
    {
        if (str1[index] >= 65 && str1[index] <= 90) {
            lower_case.push((str1[index] + 32) as u8);

        } else {
            lower_case.push(str1[index]);
        }
        assert(lower_case[index as int] == (if is_upper_case(str1[index as int]) {
            shift32_spec(str1[index as int])
        } else {
            str1[index as int]
        }));
        index += 1;
    }
    assert(forall|i: int|
        0 <= i < str1.len() ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
            shift32_spec(str1[i])
        } else {
            str1[i]
        }));
    lower_case
}

} // verus!
