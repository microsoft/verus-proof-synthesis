
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
            count_digits_recursively(text@) == count as int,
    {
        let n = text.len();
        let mut count = 0;
        let mut index = 0;
        
        while index < n
            invariant
                0 <= count,
                count <= index,
                index <= n,
                count_digits_recursively(text@.subrange(0, index as int)) == count as int,
                text.len() == n,
        {
            if is_digit(text[index]) {
                count += 1;
            }
            index += 1;
        }
        
        assert(count_digits_recursively(text@) == count as int);
        count
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5kmr9__j`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False