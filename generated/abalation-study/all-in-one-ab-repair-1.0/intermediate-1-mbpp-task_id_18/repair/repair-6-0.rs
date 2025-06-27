
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains(str: Seq<char>, key: char) -> bool
    ensures result <==> (exists |i: int| 0 <= i < str.len() && str[i] == key)
{
    exists |i: int| 0 <= i < str.len() && str[i] == key
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(#[trigger] result[i])),
        forall|i: int| 0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(#[trigger] str1[i]))
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    let ghost old_str1 = str1@;
    let ghost old_str2 = str2@;

    while index < str1.len()
        invariant
            forall|i: int| 0 <= i < index ==> (old_str2.contains(#[trigger] old_str1[i]) || output_str@.contains(#[trigger] old_str1[i])),
            forall|i: int| 0 <= i < output_str.len() ==> (old_str1.contains(#[trigger] output_str[i]) && !old_str2.contains(#[trigger] output_str[i])),
            index <= str1.len(), // Loop invariant for valid index
            output_str.len() <= index, // Loop invariant for length of output to index
    {
        if !contains(str2@, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    
    return output_str;
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmply837ja9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False