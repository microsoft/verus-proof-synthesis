
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
                0 <= count,
                count <= index, // refined invariant
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                index <= text.len()
        {
            if ((text[index] as u8) >= 48 && ((text[index] as u8) <= 57)) {
                count += 1;
            }
            index += 1;
        }
        count
    }
}

To execute this code using Verus, ensure that:
1. You have the Verus tool installed and configured properly.
2. You are using the correct command to run the verification, providing only necessary file paths.

For example, if your source file is named `count_digits.rs`, use a command like:
verus count_digits.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5w__rr53`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False