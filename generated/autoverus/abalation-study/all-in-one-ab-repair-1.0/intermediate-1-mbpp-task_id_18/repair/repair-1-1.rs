
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
            forall|k: int| 0 <= k < str.len() ==> str.inv(), // Ensures every element of str remains unchanged
            i <= str.len(), // Index i is within bounds of the vector
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(# [trigger] result[i]) && !str2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(# [trigger] str1[i]) || result@.contains(
                # [trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(
                    # [trigger] str1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(# [trigger] output_str[i])
                    && !str2@.contains(# [trigger] output_str[i])),
            forall|k: int| 0 <= k < str1.len() ==> str1.inv(), // Ensures every element of str1 remains unchanged
            forall|k: int| 0 <= k < str2.len() ==> str2.inv(), // Ensures every element of str2 remains unchanged
            index <= str1.len(), // Index within bounds
            output_str.len() <= index, // Output string length is within index
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpi27z76zk`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False