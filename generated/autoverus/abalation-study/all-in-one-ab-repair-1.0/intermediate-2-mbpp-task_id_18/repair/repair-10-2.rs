
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
                i <= str.len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier::spec]
    fn char_seq_contains(seq: Seq<char>, key: char) -> bool {
        exists|i: int| 0 <= i < seq.len() && seq[i] == key
    }

    #[verifier::loop_isolation(false)]
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
                forall|j: int|
                    0 <= j < index ==> (str2@.contains(# [trigger] str1[j]) || output_str@.contains(
                        # [trigger] str1[j],
                    )),
                forall|j: int|
                    0 <= j < output_str.len() ==> (str1@.contains(# [trigger] output_str[j])
                        && !str2@.contains(# [trigger] output_str[j])),
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1kcn96ra`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False