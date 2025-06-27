
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
                0 <= count <= index,
                0 <= index <= text.len(),
                text.len() == text.len(),
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            proof {
                assert(forall |k: int| 0 <= k < index ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
            
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }
            index += 1;

            proof {
                assert(forall |k: int| 0 <= k < index ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
        }
        
        proof {
            assert(0 <= count <= text.len());
            assert(count_uppercase_recursively(text@) == count);
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

### Explanation of Modifications:
1. **Maintained Loop Invariants Carefully**: The invariant `0 <= count <= index` and `0 <= index <= text.len()` were already correct. However, ensure that these invariants hold true at the end of each iteration.
2. **Postconditions**: Ensure the `count_uppercase_recursively` on the entire sequence is computed correctly before returning the count.
3. **Extra Proof Blocks**: Added proof blocks where necessary to help Verus understand the logical invariants and conditions more robustly.

### Debugging "Multiple Input Filenames" Error:
If the error about “multiple input filenames provided” persists, it might be related to how Verus is invoked. Ensure you are compiling and running the code with the correct cargo or Verus tool command, which might look similar to:

sh
cargo verus run


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpb_9ku0vu`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: False