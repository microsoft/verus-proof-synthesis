
use vstd::prelude::*;
fn main() {}

verus! {
    // Check if a character `key` exists in the vector `str`
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
            if (str[i] == key) {
                return true;
            }
            i += 1;
        }
        false
    }

    // Remove characters in `str1` that are also in `str2`
    fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                    #[trigger] result[i],
                )),
            forall|i: int|
                0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                    #[trigger] str1[i],
                )),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;
        
        let ghost old_str1 = str1@;
        let ghost old_str2 = str2@;
        
        while index < str1.len()
            invariant
                forall|i: int|
                    0 <= i < index ==> (old_str2.contains(#[trigger] old_str1[i]) || output_str@.contains(
                        #[trigger] old_str1[i],
                    )),
                forall|i: int|
                    0 <= i < output_str.len() ==> (old_str1.contains(#[trigger] output_str[i])
                        && !old_str2.contains(#[trigger] output_str[i])),
                index <= str1.len(), // Loop invariant for valid index
                output_str.len() <= index, // Loop invariant for length of output to index
                output_str.len() <= str1.len(), // Added by AI to help with various constraints
        {
            if (!contains(str2, str1[index])) {
                proof {
                    assert(old_str1.contains(str1[index]));
                    assert(!old_str2.contains(#[trigger] str1[index]));
                }
                output_str.push(str1[index]);
                proof {
                    assert(output_str@.len() == output_str.len() as int);
                }
            }
            index += 1;
        }

        proof {
            assert(forall|i: int| 0 <= i < output_str.len() ==> old_str1.contains(output_str[i]));
            assert(forall|i: int| 0 <= i < output_str.len() ==> !old_str2.contains(output_str[i]));
        }

        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8dyxkstr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True