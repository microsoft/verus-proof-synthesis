
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
                count <= index,
                index <= text.len(),
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                text.len() == old(text.len()),
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;
        }
        count
    }
}

### Ensure Correct Environment Setup
1. **Rust and Verus Setup:** Ensure you have a correctly configured Rust environment and have the Verus tool properly installed.
2. **Single Source File:** Ensure that you are providing the Verus tool with a single source file to avoid the `multiple input filenames provided` error.
3. **Clean Build Directory:** Clean your build directory to remove any conflicting files that could be causing issues.
4. **Run Verus Properly:** When running Verus, ensure the command is in the correct format. Typically, you would run the Verus tool on a single file like so:
    bash
    verus file.rs
   Ensure there are no typos or additional filenames being provided.

### Example Command for Verus
Try running the file explicitly from your terminal or command line interface:
bash
verus my_code.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpor_3og8m`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False