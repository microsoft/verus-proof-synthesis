
use vstd::prelude::*;
fn main() {}

verus! {
    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count,
    {
        let n = text.len();
        let mut index = 0;
        let mut count = 0;
        
        while index < n
            invariant
                0 <= count <= index, // Updated invariant for clarity
                0 <= index <= n,
                n == text.len(), // Ensuring the length remains consistent
                count_uppercase_recursively(text@.take(index as int)) == count as int,
        {
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }

            index += 1;

            proof {
                // Verify the invariant spans the entire range
                // up to the current index within loop
                assert(forall |k: int| 0 <= k < index ==> is_lower_case(text[k]) || is_upper_case(text[k]));
                assert(count <= index);
                assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
            }
        }
        
        proof {
            // Post condition proofs
            assert(count_uppercase_recursively(text@) == count as int);
        }
        
        count
    }
    
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
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmbm3kl6x`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False