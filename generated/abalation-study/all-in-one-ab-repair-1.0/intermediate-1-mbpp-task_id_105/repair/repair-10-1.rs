
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
                counter as usize <= arr.len(),
                index <= arr.len(),
                arr.len() == arr.len(),  // invariant for length consistency (considered constant)
                forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k], // arr is not modified in the loop
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
            
            proof {
                // Loop invariant verification without modifying arr should be straightforward.
                assert(count_boolean(arr@.subrange(0, index as int)) == if arr[index - 1] { (counter - 1) as int } else { counter as int });
                assert(counter as usize <= arr.len());
                assert(index <= arr.len());
                assert(arr.len() == arr.len());
                assert(forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k]);
            }
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzp0j3_1s`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 6
// Safe: False