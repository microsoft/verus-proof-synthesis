use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in a string and character, replaces blank spaces in the string with the character, and returns the string.

    assert_eq!(
        replace_blanks_with_chars(&("hello people".chars().collect()), '@')
            .iter()
            .collect::<String>(),
        "hello@people"
    );
    assert_eq!(
        replace_blanks_with_chars(&("python program language".chars().collect()), '$')
            .iter()
            .collect::<String>(),
        "python$program$language"
    );
    assert_eq!(
        replace_blanks_with_chars(&("blank space".chars().collect()), '-')
            .iter()
            .collect::<String>(),
        "blank-space"
    );
}

verus! {

fn replace_blanks_with_chars(str1: &Vec<char>, ch: char) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == 32 {
                ch
            } else {
                str1[i]
            }),
{
    let mut out_str: Vec<char> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            out_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> out_str[k] == (if str1[k] == ' ' {
                    ch
                } else {
                    str1[k]
                }),
        decreases
            str1.len() - index, 
    {
        if (str1[index] == ' ') {
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }
        index += 1;
    }
    out_str
}

} // verus!
