
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
                count_boolean(arr@.subrange(0, index as int)) == counter as int,
                counter <= arr.len() as u64,
                counter <= index as u64,
                index <= arr.len(),
                arr.len() == arr.len(),
                forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k], // arr is not modified in the loop
        {
            if (arr[index]) {
                counter += 1;
            }
            index += 1;

            proof {
                // Ensure the loop invariant conditions are upheld.
                assert(count_boolean(arr@.subrange(0, index as int)) == counter as int);
                assert(counter <= arr.len() as u64);
                assert(counter <= index as u64);
                assert(index <= arr.len());
                assert(arr.len() == arr.len());
                assert(forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k]);
            }
        }
        counter
    }
}

// Score: (1, 2)
// Safe: True