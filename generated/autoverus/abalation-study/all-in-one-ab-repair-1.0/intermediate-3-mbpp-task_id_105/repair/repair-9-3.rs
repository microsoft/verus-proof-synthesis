
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
                count_boolean(arr@.subrange(0, index as int)) == counter,
                counter as int <= index as int,
                index <= arr.len(),
                arr@.len() == old(arr).len(), // arr is not modified in the loop
        {
            if (arr[index]) {
                proof {
                    assert(count_boolean(arr@.subrange(0, index as int + 1)) ==
                               count_boolean(arr@.subrange(0, index as int)) + 1);
                }
                counter += 1;
            } else {
                proof {
                    assert(count_boolean(arr@.subrange(0, index as int + 1)) ==
                               count_boolean(arr@.subrange(0, index as int)));
                }
            }
            index += 1;
            proof {
                assert(count_boolean(arr@.subrange(0, index as int)) == counter);
            }
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpli4uiwct`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False