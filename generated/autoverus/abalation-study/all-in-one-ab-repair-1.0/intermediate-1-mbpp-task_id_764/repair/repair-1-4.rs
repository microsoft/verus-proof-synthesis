
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
            count_digits_recursively(text@.subrange(0, index as int)) == count,
            index <= text.len(),
    {
        if is_digit(text[index]) {
            count += 1;
        }
        index += 1;
    }
    count
}

} // verus!

### Key Modifications:

1. **Invariant Update:** The incorrect invariant `text.len() == text.len()` was removed (it's trivially true and doesn't add value). The remaining invariants are correctly specified and should cover the necessary logical guarantees.

2. **Utility Function:** Simplified the digit check by using the `is_digit` specification function for clarity and reuse.

### Invocation of Verus:

To ensure that Verus runs correctly, ensure the following:
1. **Single Input File:** Provide only one input file (your `.rs` file) to Verus.
2. **Tool Invocation:** Ensure the invocation command correctly points to the Verus binary and the input file.

Example correct command (assuming `verus` is your binary and `file.rs` is your input file):

sh
verus file.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmvbr_i02`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 13
// Safe: False