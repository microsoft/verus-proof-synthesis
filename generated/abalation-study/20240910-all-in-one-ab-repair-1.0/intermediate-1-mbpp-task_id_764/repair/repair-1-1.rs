
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
        // Create a ghost variable for the text sequence
        let ghost text_seq = text@; // Added by AI

        let mut count = 0;
        let mut index = 0;
        while index < text.len()
            invariant
                0 <= count <= index,
                count_digits_recursively(text_seq.subrange(0, index as int)) == count,
                index <= text.len(),
                text.len() == text.len(), // Added loop invariant specifying the length of the array
        {
            if is_digit(text[index]) {
                count += 1;
            }
            index += 1;

            proof {
                assert(count_digits_recursively(text_seq.subrange(0, index as int)) == count);
            } // Added invariant proving block
        }

        // Post-condition proof block
        proof {
            assert(count_digits_recursively(text_seq) == count);
        }

        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdbxkl9cs`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False