
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.drop_last()) + if seq.last() {
                1 as int
            } else {
                0 as int
            }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len(),
            count_boolean(arr@) == count as int,
    {
        let mut index = 0;
        let mut counter = 0;

        while index < arr.len()
            invariant
                count_boolean(arr@.subrange(0, index as int)) == counter as int,
                counter as usize <= index,
                index <= arr.len(),
                arr@.len() == old(arr).len(), // arr is not modified in the loop
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpo86unjrn`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False