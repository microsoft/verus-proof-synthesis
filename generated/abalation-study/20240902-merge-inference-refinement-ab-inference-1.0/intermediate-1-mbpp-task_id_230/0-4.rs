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
            forall |i:int| 
                0 <= i < index 
                ==> out_str[i] == (if str1[i] == (' ' as char) { ch } else { str1[i] }),
            str1.len() == old(str1).len(),
    {
        if str1[index] == (' ' as char) {
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }
        index += 1;
    }

    out_str
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1