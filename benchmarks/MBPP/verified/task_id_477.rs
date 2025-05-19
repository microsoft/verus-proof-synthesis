use vstd::prelude::*;

fn main() {
    // Write a function in Rust to convert the given string to lower case.

    assert_eq!(
        to_lowercase(&("InValid".chars().collect()))
            .iter()
            .collect::<String>(),
        "invalid"
    );
    assert_eq!(
        to_lowercase(&("TruE".chars().collect()))
            .iter()
            .collect::<String>(),
        "true"
    );
    assert_eq!(
        to_lowercase(&("SenTenCE".chars().collect()))
            .iter()
            .collect::<String>(),
        "sentence"
    );
}

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
            0 <= index <= str1.len(),
            lower_case.len() == index,
            forall|i: int|
                0 <= i < index ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
                    shift32_spec(str1[i])
                } else {
                    str1[i]
                }),
        decreases
            str1.len() - index,
    {
        if (str1[index] >= 'A' && str1[index] <= 'Z') {
            lower_case.push(((str1[index] as u8) + 32) as char);

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
