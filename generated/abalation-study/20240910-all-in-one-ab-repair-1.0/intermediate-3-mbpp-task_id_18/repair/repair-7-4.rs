
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
            str.len() == old(str.len()), // Ensures the length of str doesn't change
            i <= str.len(),
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
        forall|i: int| 0 <= i < result.len() ==> (str1@.contains(result[i]) && !str2@.contains(result[i])),
        forall|i: int| 0 <= i < str1.len() ==> (str2@.contains(str1[i]) || result@.contains(str1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int| 0 <= i < index ==> (str2@.contains(str1[i]) || output_str@.contains(str1[i])),
            forall|i: int| 0 <= i < output_str.len() ==> (str1@.contains(output_str[i]) && !str2@.contains(output_str[i])),
            str1.len() == old(str1.len()), // Ensures the length of str1 doesn't change
            str2.len() == old(str2.len()), // Ensures the length of str2 doesn't change
            index <= str1.len(), // Necessary to ensure index stays within valid bounds
            output_str.len() <= index, // Ensures output_str's length does not exceed the current index
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpun82mdsa`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False