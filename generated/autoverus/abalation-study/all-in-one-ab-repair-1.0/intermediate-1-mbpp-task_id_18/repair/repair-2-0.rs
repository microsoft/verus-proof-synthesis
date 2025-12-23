
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
            i <= str.len(), // Assertion covered
            str.len() == str.len(), // Loop invariant for the array length Declaration error fixed
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
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(
                    # [trigger] str1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(# [trigger] output_str[i])
                    && !str2@.contains(# [trigger] output_str[i])),
            index <= str1.len(), // Fixed index invariant for conditions
            str1.len() == str1.len(), // Loop invariant for the array length
            str2.len() == str2.len(), // Loop invariant for the array length
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprr3200dg`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: False