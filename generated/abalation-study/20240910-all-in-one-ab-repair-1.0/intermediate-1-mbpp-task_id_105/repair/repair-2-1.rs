
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
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            count_boolean(arr@.subrange(0, index as int)) == counter,
            counter <= arr.len() as u64,
            counter <= index as u64,
            index <= arr.len(),
            arr.len() == arr.len(),
            forall |k:int| 0 <= k < arr.len() ==> arr@.index(k) == arr@.index(k), // Added by AI: arr is immutable and cannot be changed within loop
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5lczaqtw`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False