
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
    let mut counter: u64 = 0;
    while index < arr.len()
        invariant
            count_boolean(arr@.subrange(0, index as int)) == counter as int, // Ensure the count matches.
            counter as usize <= arr.len(), // Ensure the counter is within the array length.
            index <= arr.len(), // Ensure the index is within the array length.
    {
        if arr[index] {
            counter += 1;
        }
        index += 1;
    }
    assert(count_boolean(arr@) == counter as int); // Ensure the final count.
    counter
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0sh7_wrr`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5
// Safe: False