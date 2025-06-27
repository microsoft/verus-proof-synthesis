
use vstd::prelude::*;
fn main() {}

verus! {
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
                index <= text.len(),
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                text.len() == text.len(),  // fixed invariant to match the text's length
        {
            if is_digit(text[index]) {
                count += 1;
            }
            index += 1;

            // Proof block to ensure the invariants hold
            proof {
                assert(0 <= count);  // Ensure count is non-negative
                assert(count <= index);  // Ensure count is never more than index
                assert(index <= text.len());  // Ensure index remains within bounds

                let sub_seq = text@.subrange(0, index as int);
                assert(count_digits_recursively(sub_seq) == count);  // Ensure count reflects the recursive digit count
            }
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqpetfdyh`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False