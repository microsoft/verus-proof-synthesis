
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
            counter <= arr.len() as int, // modified
            counter <= index as int, // modified
            index <= arr.len(), // kept
            arr.len() == arr.len(), // kept
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // kept
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    counter as u64
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn7w51aav`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: False