use vstd::prelude::*;

fn main() {}

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
            index <= str1.len(),
            out_str.len() == index,
            forall |i: int| 0 <= i < index ==> 
                out_str[i] == (if str1[i] == ' ' {
                    ch
                } else {
                    str1[i]
                }),
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
// Score: (2, 0)
// Safe: True