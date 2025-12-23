
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)] // This is generally for performance optimizations in proofs

    spec fn is_digit(c: char) -> bool {
        (c as u8) >= 48 && (c as u8) <= 57
    }

    spec fn count_digits_recursively(seq: Seq<char>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_digits(text: &Vec<char>) -> (count: usize)
        ensures
            0 <= count <= text.len(),
            count_digits_recursively(text@) == count,
    {
        let mut count = 0;
        let mut index = 0;
        while index < text.len()
            invariant
                0 <= count <= index,
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                index <= text.len(),
                text.len() == text.len(), // Right boundary invariant.
        {
            if is_digit(text[index]) {  // Using is_digit function for consistency
                count += 1;
            }
            index += 1;
        }
        count
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpxgux8mb6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False