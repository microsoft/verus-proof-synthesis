
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
                1
            } else {
                0
            }
        }
    }

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
                0 <= count as usize <= index,
                0 <= index <= n,
                text.len() == n, // invariant on text length being equal to its original length
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                // Ensure that every character processed so far is either lowercase or uppercase
                forall |k: int| 0 <= k < index as int ==> is_lower_case(text@[k]) || is_upper_case(text@[k]),
        {
            if is_upper_case(text[index]) {
                count += 1;
            }
            index += 1;
        }
        count
    }
}

#### Running Verus Correctly

Make sure you are running the Verus tool correctly. Here’s a standard way to compile and execute Verus code:

1. **Ensure Verus is installed and configured correctly** in your environment. Verify this by running `verus --version` or a similar command.

2. **Compile and run the Verus file**. If you use a command line, make sure to specify only one input file. An example command might look like:
   sh
   verus yourfile.rs
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgft5y9it`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False