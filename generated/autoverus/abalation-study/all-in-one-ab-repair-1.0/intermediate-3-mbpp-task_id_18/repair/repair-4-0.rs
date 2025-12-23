
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
            forall|i: int|
                0 <= i < result.len() ==> (exists|j: int| 0 <= j < str1.len() && result[i] == str1[j]) &&
                forall|j: int| 0 <= j < str2.len() ==> result[i] != str2[j],
            forall|i: int|
                0 <= i < str1.len() ==> (exists|j: int| 0 <= j < result.len() && str1[i] == result[j]) ||
                (exists|j: int| 0 <= j < str2.len() && str1[i] == str2[j]),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < str1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (exists|j: int| 0 <= j < str2.len() && str1[i] == str2[j]) ||
                                        (exists|j: int| 0 <= j < output_str.len() && str1[i] == output_str[j]),
                forall|i: int|
                    0 <= i < output_str.len() ==> (exists|j: int| 0 <= j < str1.len() && output_str[i] == str1[j]) &&
                                                  forall|j: int| 0 <= j < str2.len() ==> output_str[i] != str2[j],
                index <= str1.len(),
                output_str.len() <= index,
        {
            if !contains(str2, str1[index]) {
                output_str.push(str1[index]);
            }
            index += 1;
        }
        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzrd_q5q7`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False