
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
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
                text.len() == text.len()
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;
        }
        count
    }

} // verus!

### Check the Environment:
- **Multiple Input Filenames:**
  The error message suggests multiple filenames are being passed to the compiler or interpreter. Ensure that you're running the script with the correct single input. For example:
  sh
  verus example.rs
  Verify no redundant files or paths are being interpreted.

### Run Verus Correctly:
1. **Single File Execution:**
   If you are executing the Verus tool, ensure you're specifying only one file at a time.
   sh
   verus count_digits.rs
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8bqz_11l`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False