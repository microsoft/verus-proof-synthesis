
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    spec fn is_lower_case(c: char) -> bool {
        (c as u32) >= 97 && (c as u32) <= 122
    }

    spec fn is_upper_case(c: char) -> bool {
        (c as u32) >= 65 && (c as u32) <= 90
    }

    spec fn count_uppercase_recursively(seq: Seq<char>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count as int,
    {
        let mut index = 0;
        let mut count = 0;
        while index < text.len()
            invariant
                0 <= count as int <= index as int,
                0 <= index as int <= text.len() as int,
                text.len() == text.len(),
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                // Adding invariant for all elements in the array since there is no x.set() in the loop
                forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }
            index += 1;

            // Proof of invariants being maintained
            proof {
                assert(0 <= count as int);
                assert(count as int <= index as int);
                assert(0 <= index as int <= text.len() as int);
                assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
                assert(forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
        }
        count
    }
}

### Steps to Ensure Correct Verus Invocation
To resolve the tool invocation error, please make sure you are running the Verus tool correctly, particularly if it's part of a build or CI process. Here is a reminder of how to typically invoke Verus:

1. Save the Rust code to a file, e.g., `main.rs`.
2. Use the Verus command line tool to check the file, typically:
   
   sh
   verus --some-verus-flags `main.rs`
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0wlrkz62`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False