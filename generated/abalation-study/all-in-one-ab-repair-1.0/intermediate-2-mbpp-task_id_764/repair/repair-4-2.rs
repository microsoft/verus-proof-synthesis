
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
            count_digits_recursively(seq.subrange(0, seq.len() - 1)) + 
            if is_digit(seq.index(seq.len() - 1)) {
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
                0 <= index <= text.len(),
                0 <= count,
                count <= index,
                count_digits_recursively(text@.subrange(0, index as int)) == count,
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;

            proof {
                assert(0 <= count); // Ensure count is non-negative
                assert(count <= index); // Ensure count is never more than index
                assert(index <= text.len()); // Ensure index remains within bounds
                assert(count_digits_recursively(text@.subrange(0, index as int)) == count); // Ensure count reflects the recursive digit count
            }
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkst7nw7r`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True