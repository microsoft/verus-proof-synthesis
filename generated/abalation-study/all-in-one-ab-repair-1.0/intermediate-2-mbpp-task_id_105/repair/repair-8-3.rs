
use vstd::prelude::*;
fn main() {}

verus! {

    spec fn count_boolean(seq: Seq<bool>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.drop_last()) + if (seq.last()) {
                1 as int
            } else {
                0 as int
            }
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
                index <= arr.len(),
                counter <= arr.len(),
                // Instead of using `==>` perhaps use `==` for preventing modification
                forall |k: int| 0 <= k < index ==> arr@.index(k) == (if arr[k] { 1 } else { 0 }),
                index as int == counter == count_boolean(arr@.subrange(0, index as int)),
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmnp979ei`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False