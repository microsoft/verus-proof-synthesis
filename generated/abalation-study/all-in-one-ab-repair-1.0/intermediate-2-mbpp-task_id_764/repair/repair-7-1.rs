
use vstd::prelude::*;

fn main() {}

verus! {
    // Function to check if a character is a digit
    spec fn is_digit(c: char) -> bool {
        (c as u8) >= 48 && (c as u8) <= 57
    }

    // Recursive function to count digits in a sequence of characters
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
                0 <= count <= index,
                count_digits_recursively(text@.subrange(0, index as int)) == count,
                index <= text.len(),
                text.len() == text.len(),
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;

            proof {
                assert(0 <= count);
                assert(count <= index);
                assert(count_digits_recursively(text@.subrange(0, index as int)) == count);
                assert(index <= text.len());
                assert(text.len() == text.len());
            }
        }

        proof {
            assert(0 <= count);
            assert(count <= text.len());
            assert(count_digits_recursively(text@) == count);
        }

        count
    }
}

Make sure to focus on the command or script you're using to compile/verifying this Verus program. You should ensure that the build or execution command does not mistakenly include multiple input files unless that is the intended behavior. Here is a generic command snippet that might be relevant based on your setup:

verus filename.rs --option1 --option2


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp33k9phhq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False