
use vstd::prelude::*;
fn main() {}

verus! {
    
    #[verifier::loop_isolation(false)]
    
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
                1
            } else {
                0
            }
        }
    }
    
    fn count_uppercase(text: &Vec<char>) -> (count: u64)
        ensures
            0 <= count <= text.len(),
            count_uppercase_recursively(text@) == count as int,
    {
        let mut index = 0;
        let mut count = 0;
        let n = text.len();
        while index < n
            invariant
                0 <= count <= index,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps7ywvmsq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False