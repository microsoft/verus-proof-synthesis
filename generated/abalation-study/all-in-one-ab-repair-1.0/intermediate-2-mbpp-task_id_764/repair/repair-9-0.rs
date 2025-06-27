
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
                text.len() == text.len(), // This invariant is trivial but necessary for the proof checker
        {
            if is_digit(text[index]) {
                count += 1;
            }
            index += 1;
            proof {
                // Maintain invariant: count_digits_recursively(text@.subrange(0, index as int)) == count
                assert(0 <= index <= text.len()); // Index bounds
                assert(0 <= count <= index); // Count bounds
                
                // Establish that the invariants are maintained correctly
                if is_digit(text[index - 1]) {
                    assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
                } else {
                    assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
                }
            }
        }

        // Proof check at the end of the function body
        proof {
            assert(0 <= count);
            assert(count <= text.len());
            assert(count_digits_recursively(text@) == count);
        }

        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjo0091s1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False