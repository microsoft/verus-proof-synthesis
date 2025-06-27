
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int {
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.subrange(0, seq.len() - 1)) + if seq[seq.len() - 1] { 1 } else { 0 }
        }
    }

    fn count_true(arr: &Vec<bool>) -> (count: u64)
        ensures
            0 <= count <= arr.len(),
            count_boolean(arr@) == count,
    {
        let n = arr.len();
        let mut index = 0;
        let mut counter = 0;
        while index < n
            invariant
                0 <= index <= n,
                counter <= n,
                count_boolean(arr@.subrange(0, index as int)) == counter,
                arr.len() == n, // arr.len() does not change
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter as u64
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpbklmkipz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False