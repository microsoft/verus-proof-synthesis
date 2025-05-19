use vstd::prelude::*;

fn main() {
    // Write a function in Rust  to replace characters in a string.

    assert_eq!(
        replace_chars(&("polygon".chars().collect()), 'y', 'l')
            .iter()
            .collect::<String>(),
        "pollgon"
    );
    assert_eq!(
        replace_chars(&("character".chars().collect()), 'c', 'a')
            .iter()
            .collect::<String>(),
        "aharaater"
    );
    assert_eq!(
        replace_chars(&("python".chars().collect()), 'l', 'a')
            .iter()
            .collect::<String>(),
        "python"
    );
}

verus! {

fn replace_chars(str1: &Vec<char>, old_char: char, new_char: char) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == old_char {
                new_char
            } else {
                str1[i]
            }),
{
    let mut result_str = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1@.len(),
            result_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> result_str[k] == (if str1[k] == old_char {
                    new_char
                } else {
                    str1[k]
                }),
        decreases
            str1.len() - index,
    {
        if str1[index] == old_char {
            result_str.push(new_char);
        } else {
            result_str.push(str1[index]);
        }
        index += 1;
    }
    result_str
}

} // verus!
