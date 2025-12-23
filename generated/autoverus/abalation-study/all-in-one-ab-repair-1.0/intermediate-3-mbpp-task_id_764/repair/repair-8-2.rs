
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
            count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) { 1 } else { 0 }
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
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                index <= text.len(),
                text.len() == old(text.len())
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;
        }

        // Assert that the invariant holds at the loop exit
        proof {
            assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
        }

        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7b9n9rjc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True