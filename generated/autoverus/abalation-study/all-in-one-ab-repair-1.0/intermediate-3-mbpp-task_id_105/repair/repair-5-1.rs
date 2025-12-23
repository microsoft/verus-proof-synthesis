
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn count_boolean(seq: Seq<bool>) -> int
        decreases seq.len(),
    {
        if seq.len() == 0 {
            0
        } else {
            count_boolean(seq.subrange(0, seq.len() - 1)) + if seq.last() {
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
        let n = arr.len();
        let mut index = 0;
        let mut counter = 0;

        while index < n
            invariant
                count_boolean(arr@.subrange(0, index as int)) == counter as int,
                counter as usize <= index, // updated counter type to usize for comparability reasons
                index <= n,
                arr@.len() == n as int, 
        {
            if arr[index] {
                counter += 1;
            }
            index += 1;
        }
        counter as u64
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl6zrynsy`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5
// Safe: False