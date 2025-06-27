
use vstd::prelude::*;
fn main() {}

verus! {
    
    spec fn count_boolean(seq: Seq<bool>) -> int {
        decreases seq.len(),
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.drop_last()) + if seq.last() { 1 } else { 0 }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len(),
            count_boolean(arr@) == count,
    {
        let mut index = 0;
        let mut counter = 0;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                0 <= counter <= index,
                count_boolean(arr@.subrange(0, index as int)) == counter,
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp43rvh6d6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False