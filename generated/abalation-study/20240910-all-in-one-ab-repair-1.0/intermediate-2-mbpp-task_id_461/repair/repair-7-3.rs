
use vstd::prelude::*;
fn main() {}

verus! {
    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len() as u64,
            count_uppercase_recursively(text@) == count as int,
    {
        let mut index = 0;
        let mut count = 0;
        let text_len = text.len(); // Capture the length to use in proof
        while index < text_len
            invariant
                0 <= count <= index as u64,
                0 <= index <= text_len,
                text_len == text.len(),
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                forall |k: int| 0 <= k < index as int ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if is_upper_case(text[index]) {
                count += 1;
            }
            index += 1;

            proof {
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

### Key Changes

1. **Ensures Clause:** Ensure `count` is within the length bounds of `text`.
   rust
   ensures
       0 <= count <= text.len() as u64,
       count_uppercase_recursively(text@) == count as int,

2. **Invariant Clause:**
   - Ensure count is non-negative and within current index.
   - `index` variable is captured and managed correctly during the loop.
   rust
   invariant
       0 <= count <= index as u64,
       0 <= index <= text_len,
       text_len == text.len(),
       count_uppercase_recursively(text@.take(index as int)) == count as int,
       forall |k: int| 0 <= k < index as int ==> is_lower_case(text[k]) || is_upper_case(text[k]),
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqwfvja_v`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False