
use vstd::prelude::*;
fn main() {}
verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.subrange(0, seq.len() - 1)) + if seq.index(seq.len() - 1) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count as int, // We need to convert `u64` to `int` for comparison
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            count_boolean(arr@.subrange(0, index as int)) == counter as int, // invariant adjusted to type `int`
            counter as usize <= arr.len(), // invoking the bound check
            index <= arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k as usize] == arr[k as usize], // arr is not modified in the loop
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp70c6r5nl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False