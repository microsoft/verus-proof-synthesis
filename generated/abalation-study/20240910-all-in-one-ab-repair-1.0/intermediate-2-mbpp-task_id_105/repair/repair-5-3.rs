
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
        count_boolean(seq.drop_last()) + if seq.last() { 1 } else { 0 }
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
            counter <= index,
            index <= n,
            forall |k: int| 0 <= k < n ==> arr[k] == arr[k], // arr is not modified in the loop
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    return counter;
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkia0wqsy`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False