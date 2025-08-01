
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
        let n = text.len();
        let mut count: usize = 0;
        let mut index: usize = 0;
        while index < n
            invariant
                0 <= index <= n,
                0 <= count <= index,
                count_digits_recursively(text@[0..index as int]) == count,
                text.len() == n,
        {
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1;
            }
            index += 1;
        }
        
        proof {
            assert(count_digits_recursively(text@[0..index as int]) == count);
            assert(count_digits_recursively(text@) == count); // Final proof ensures count matches the recursive digit count
        }
        
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnxsqn4u6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False