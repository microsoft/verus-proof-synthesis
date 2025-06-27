use vstd::prelude::*;

fn main() {}

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
            index <= str1.len(),
            result_str.len() == index,
            str1.len() == old(result_str).capacity(), //The capacity of result_str will always be the length of str1
            forall|i: int| 0 <= i < index ==>
                result_str[i] == (if str1[i] == old_char {
                    new_char
                } else {
                    str1[i]
                }),
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
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1