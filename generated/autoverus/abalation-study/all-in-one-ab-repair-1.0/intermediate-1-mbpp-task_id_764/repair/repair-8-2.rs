
use vstd::prelude::*;
fn main() {}

verus! {
    // Spec function to check if a character is a digit
    spec fn is_digit(c: char) -> bool {
        (c as u8) >= 48 && (c as u8) <= 57
    }

    // Recursive specification function to count digits in a sequence
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

    // Function to count digits in a vector of characters
    fn count_digits(text: &Vec<char>) -> (count: usize)
        ensures
            0 <= count <= text.len(),
            count_digits_recursively(text@) == count,
    {
        let mut count = 0;
        let mut index = 0;
        while index < text.len()
            invariant
                0 <= count,
                count <= index,
                index <= text.len(),
                // The invariant captures all digits counted in the current processed subrange
                count_digits_recursively(text@.subrange(0, index as int)) == count,
        {
            if is_digit(text[index]) {
                count += 1;
            }
            index += 1;
        }
        count
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7ba4btsb`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False