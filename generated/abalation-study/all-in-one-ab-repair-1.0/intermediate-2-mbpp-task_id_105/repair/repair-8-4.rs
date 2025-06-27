
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int {
        decreases(seq.len());
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.drop_last()) + if seq.last() { 1 } else { 0 }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len() as u64,
            count_boolean(arr@) == count as int,
    {
        let mut index = 0;
        let mut counter = 0;
        while index < arr.len()
            invariant
                count_boolean(arr@.subrange(0, index as int)) == counter,
                counter <= arr.len() as u64,
                counter <= index as u64,
                index < arr.len(),
                arr.len() == arr.len(),
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2gd51vtu`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False