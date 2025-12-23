
use vstd::prelude::*;
fn main() {}

verus! {
// Function to check if a vector contains a specified character
fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),  // Loop invariant for valid i
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

// Function to remove characters from str1 that are present in str2
fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        // Ensuring that the resulting vector does not contain any character from str2
        forall|i: int| 0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(#[trigger] result[i])),
        // Ensuring that every character of str1 is either in str2 or in the result vector
        forall|i: int| 0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(#[trigger] str1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            // Ensuring all characters in str1 until current index are checked against the conditions
            forall|i: int| 0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(#[trigger] str1[i])),
            // Ensuring all characters in output_str satisfy the same conditions
            forall|i: int| 0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i]) && !str2@.contains(#[trigger] output_str[i])),
            index <= str1.len(), // Loop invariant for valid index
            output_str.len() <= index, // Loop invariant for length of output to index
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr0o46f4v`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: False