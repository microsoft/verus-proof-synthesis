
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::proof]
    #[verifier::accept_recursive]
    spec fn is_lower_case(c: char) -> bool {
        (c as u32) >= 97 && (c as u32) <= 122
    }

    #[verifier::proof]
    #[verifier::accept_recursive]
    spec fn is_upper_case(c: char) -> bool {
        (c as u32) >= 65 && (c as u32) <= 90
    }

    #[verifier::proof]
    #[verifier::accept_recursive]
    spec fn count_uppercase_recursively(seq: Seq<char>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) { 1 } else { 0 }
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
                0 <= index <= n,
                0 <= count as usize <= index,
                count_uppercase_recursively(text@.take(index as int)) == count as int,
        {
            if is_upper_case(text[index]) {
                count += 1;
            }
            index += 1;
        }

        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpj7xlg3ao`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False