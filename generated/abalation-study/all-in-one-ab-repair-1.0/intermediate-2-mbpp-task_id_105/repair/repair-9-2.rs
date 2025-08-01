
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            if seq.last() {
                count_boolean(seq.drop_last()) + 1
            } else {
                count_boolean(seq.drop_last())
            }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len() as u64,
            count_boolean(arr@) == count as int,
    {
        let n = arr.len();
        let mut index: usize = 0;
        let mut counter: u64 = 0;
        while index < arr.len()
            invariant
                count_boolean(arr@[0..index as int]) == counter as int,
                0 <= counter <= n as u64,
                0 <= index <= n,
                arr.len() == n,
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgqudyj94`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False