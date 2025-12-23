
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains_spec(str: Seq<char>, key: char) -> bool {
    exists|i: int| 0 <= i < str.len() && str[i] == key
}

fn contains(str: &Vec<char>, key: char) -> bool
    ensures
        result == contains_spec(str@, key),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
            str.len() == str.len(), // Maintaining length invariant
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> Vec<char>
    ensures
        forall|i: int|
            0 <= i < result@.len() ==> (contains_spec(str1@, result@[i]) && !contains_spec(str2@, result@[i])),
        forall|i: int|
            0 <= i < str1@.len() ==> (contains_spec(str2@, str1@[i]) || contains_spec(result@, str1@[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (contains_spec(str2@, str1@[i]) || contains_spec(output_str@, str1@[i])),
            forall|i: int|
                0 <= i < output_str.len() ==> (contains_spec(str1@, output_str@[i]) && !contains_spec(str2@, output_str@[i])),
            index <= str1.len(),
            output_str.len() <= index, // Ensures invariance of length
            str1.len() == str1.len(),
            str2.len() == str2.len(),
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzv8n45er`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False