
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
                0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(#[trigger] result[i])),
            forall|i: int|
                0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(#[trigger] str1[i])),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        while index < str1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(#[trigger] str1[i])),
                forall|i: int|
                    0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i])
                        && !str2@.contains(#[trigger] output_str[i])),
                index <= str1.len(),
                output_str.len() <= index,
        {
            proof {
                let output_str_len = output_str.len();
                if index < str1.len() {
                    assert(0 <= index < str1.len());
                }
            }
            if !contains(str2, str1[index]) {
                proof {
                    assert(forall|i: int| 0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i]) && !str2@.contains(#[trigger] output_str[i])));
                }
                output_str.push(str1[index]);
                proof {
                    assert(output_str.len() == output_str_len + 1);
                    assert(str1@.contains(#[trigger] str1[index]) && !str2@.contains(#[trigger] str1[index]));
                }
            }
            index += 1;
            proof {
                assert(index <= str1.len());
                assert(output_str.len() <= index);
            }
        }
        result
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfifytxjl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False