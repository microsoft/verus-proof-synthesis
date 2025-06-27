
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_lower_case(c: char) -> bool {
        (c as u32) >= 97 && (c as u32) <= 122
    }
    
    spec fn is_upper_case(c: char) -> bool {
        (c as u32) >= 65 && (c as u32) <= 90
    }
    
    spec fn count_uppercase_recursively(seq: Seq<char>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }
    
    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len() as u64,
            count_uppercase_recursively(text@) == count as int,
    {
        let n = text.len();
        let mut index = 0;
        let mut count = 0;
        while index < n
            invariant
                0 <= count <= index as u64,
                0 <= index <= n,
                count_uppercase_recursively(text@.take(index as int)) == count as int,
        {
            if is_upper_case(text[index]) {
                count += 1;
            }
            index += 1;
        }
        count
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp6o73e5ti`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False