
use vstd::prelude::*;
fn main() {}

verus! {
    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count,
    {
        let mut index = 0;
        let mut count = 0;
        while index < text.len()
            invariant
                0 <= count as int <= index as int,
                0 <= index <= text.len(),
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                forall |k: int| 0 <= k < index as int ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }

            index += 1;

            proof {
                // This proof block is to ensure that the invariant that was checking for lower and upper case holds.
                assert(forall |k: int| 0 <= k < index as int ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnapcw4bi`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True