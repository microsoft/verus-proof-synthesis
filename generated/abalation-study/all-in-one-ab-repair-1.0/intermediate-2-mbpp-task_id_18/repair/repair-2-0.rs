
use vstd::prelude::*;
fn main() {}

verus! {
    // The contains function should satisfy the logical conditions you've specified.
    // Let's add some local invariants to help Rust understand the logic flows here.

    spec fn contains_invariant(str: Seq<char>, key: char, index: int) -> bool {
        forall|j: int| 0 <= j < index ==> str[j] != key
    }

    fn contains(str: &Vec<char>, key: char) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                contains_invariant(str@, key, i as int),
                forall|k: int| 0 <= k < str.len() ==> str[k] == str[k],
                i <= str.len(),
                str.len() == str.len(),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    // Let's handle the remove_chars function here as well and ensure the invariants are correct.
    // Added additional proof blocks and invariants.

    spec fn remove_chars_invariant(str1: Seq<char>, str2: Seq<char>, output_str: Seq<char>, index: int) -> bool {
        forall|i: int| 0 <= i < index ==> (str2.contains(str1[i]) || output_str.contains(str1[i]))
            && forall|i: int| 0 <= i < output_str.len() ==> (str1.contains(output_str[i]) && !str2.contains(output_str[i]))
    }

    fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
        ensures
            result@.len() <= str1@.len(),
            forall|i: int| 
                0 <= i < result@.len() ==> (str1@.contains(result@[i]) && !str2@.contains(result@[i])),
            forall|i: int| 
                0 <= i < str1@.len() ==> (str2@.contains(str1@[i]) || result@.contains(str1@[i])),
    {
        let mut output_str = Vec::new();
        let mut index = 0;

        while index < str1.len()
            invariant
                remove_chars_invariant(str1@, str2@, Seq::from_vec(output_str.clone()), index as int),
                forall|k: int| 0 <= k < str1.len() ==> str1[k] == str1[k],
                forall|k: int| 0 <= k < str2.len() ==> str2[k] == str2[k],
                index <= str1.len(),
                output_str.len() <= index,
                str1.len() == str1.len(),
                str2.len() == str2.len(),
        {
            if !contains(str2, str1[index]) {
                proof {
                    assert(contains_invariant(str2@, str1[index], index as int + 1));
                }
                output_str.push(str1[index]);
            }
            index += 1;
        }

        output_str
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp36ylds4g`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False