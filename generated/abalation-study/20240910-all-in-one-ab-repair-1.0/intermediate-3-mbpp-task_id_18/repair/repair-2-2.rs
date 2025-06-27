
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            forall |k:int| 0 <= k < str.len() ==> str[k] == str[k], // Covered invariant for array str
            i <= str.len(),
            str.len() == str.len(), // Loop invariant for the array length
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
        forall|i: int|
            0 <= i < result.len() ==> (exists|j: int| 0 <= j < str1.len() && #[trigger] (str1[j] == result[i]) && !(exists|k: int| 0 <= k < str2.len() && #[trigger] (str2[k] == result[i]))),
        forall|i: int|
            0 <= i < str1.len() ==> !(exists|j: int| 0 <= j < str2.len() && #[trigger] str2[j] == str1[i]) || (exists|k: int| 0 <= k < result.len() && #[trigger] result[k] == str1[i]),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> !(exists|j: int| 0 <= j < str2.len() && #[trigger] str2[j] == str1[i]) || (exists|k: int| 0 <= k < output_str.len() && #[trigger] output_str[k] == str1[i]),
            forall|i: int|
                0 <= i < output_str.len() ==> (exists|j: int| 0 <= j < str1.len() && #[trigger] str1[j] == output_str[i]) && !(exists|k: int| 0 <= k < str2.len() && #[trigger] str2[k] == output_str[i]),
            forall |k:int| 0 <= k < str1.len() ==> str1[k] == str1[k], // Covered invariant for array str1
            forall |k:int| 0 <= k < str2.len() ==> str2[k] == str2[k], // Covered invariant for array str2
            index <= str1.len(),
            output_str.len() <= index,
            str1.len() == str1.len(), // Loop invariant for the array length
            str2.len() == str2.len(), // Loop invariant for the array length
    {
        if (!contains(str2, str1[index])) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmplwdfr62x`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False