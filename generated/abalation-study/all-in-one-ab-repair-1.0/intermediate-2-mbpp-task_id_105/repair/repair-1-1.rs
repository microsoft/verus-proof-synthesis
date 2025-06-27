
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int {
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.drop_last()) + if seq.last() { 1 } else { 0 }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len(),
            count_boolean(arr@) == count as int,
    {
        let arr_len = arr.len() as int; // Cast to int for consistency in specs and assertions
        let mut index: u64 = 0;
        let mut counter: u64 = 0;
        while index < arr.len()
            invariant
                count_boolean(arr@.subrange(0, index as int)) == counter as int,
                counter as int <= arr_len,
                index as int <= arr_len,
                forall |k: int| 0 <= k < arr_len ==> arr[k as usize] == arr[k as usize], // arr is not modified in the loop
        {
            if arr[index as usize] { // Ensure index is appropriately cast to usize
                counter += 1;
            }
            index += 1;
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqwt8ijn4`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False