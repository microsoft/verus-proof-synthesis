
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
            0 <= count <= text.len() as u64, // Corrected comparison with text.len()
            count_uppercase_recursively(text@) == count as int, // Ensures the equality in integer form
    {
        let n = text.len();
        let mut index = 0;
        let mut count = 0;
        while index < n
            invariant
                0 <= count as usize <= index,
                0 <= index <= n,
                text.len() == n,
                count_uppercase_recursively(text@.take(index as int)) == count as int,
                forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]),
        {
            if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
                count += 1;
            }
            index += 1;

            proof {
                assert(0 <= count as int);
                assert(count as int <= index as int);
                assert(0 <= index as int <= n as int);
                assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
                assert(forall |k: int| 0 <= k < n as int ==> is_lower_case(text[k]) || is_upper_case(text[k]));
            }
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpcwwa9je6`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 6
// Safe: False