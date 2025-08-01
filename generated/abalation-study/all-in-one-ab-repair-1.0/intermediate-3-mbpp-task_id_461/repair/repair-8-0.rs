
use vstd::prelude::*;
fn main() {}

verus! {
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
            count_uppercase_recursively(seq.subrange(0, seq.len() - 1)) + if is_upper_case(seq[seq.len() - 1]) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count,
    {
        let n = text.len();
        let mut index: usize = 0;
        let mut count: u64 = 0;
        
        while index < n
            invariant
                0 <= index <= n,
                0 <= count <= index as u64,
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                // Ensure that if index is within bounds, the character is either lowercase or uppercase
                forall |k: int| 0 <= k < n ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if is_upper_case(text[index]) {
                count += 1;
            }
            index += 1;

            proof {
                assert(0 <= count as int);
                assert(count as int <= index as int);
                assert(0 <= index as int <= text.len() as int);
                assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
            }
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn1de7kse`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False