
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
                count_digits_recursively(text@.subrange(0, index as int)) == count,
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;
        }
        count
    }

} // verus!

If you are still encountering the "multiple input filenames provided" error, ensure that:

1. You are invoking the Verus tool with the correct command-line arguments.
2. No unintended command-line arguments or environment settings are causing the issue.

To run the above code using Verus, you should be using the `cargo-verus` tool or an equivalent command, ensuring the correct single file is specified:

sh
cargo verus run --bin your_binary_name


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7c3s0ofc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False