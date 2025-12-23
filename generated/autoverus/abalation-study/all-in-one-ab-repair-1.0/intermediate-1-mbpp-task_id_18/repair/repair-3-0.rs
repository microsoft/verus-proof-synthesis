
use vstd::prelude::*;
fn main() {}

verus! {

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            forall|k: int| 0 <= k < str.len() ==> str[k] == str[k],
            i <= str.len(), 
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@.len() == str1@.len() - str2@.count(|c| str1@.contains(c)),
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(
                    #[trigger] str1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i])
                    && !str2@.contains(#[trigger] output_str[i])),
            forall|k: int| 0 <= k < str1.len() ==> str1[k] == str1[k],
            forall|k: int| 0 <= k < str2.len() ==> str2[k] == str2[k],
            index <= str1.len(),
            output_str.len() <= index,
    {
        if (!contains(str2, str1[index])) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpy1up0hfj`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False