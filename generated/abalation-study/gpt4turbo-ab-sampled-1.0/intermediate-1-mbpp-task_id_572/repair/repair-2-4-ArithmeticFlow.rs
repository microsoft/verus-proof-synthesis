
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
            arr.len() == arr.len(), // loop invariant that specifies the length of the array arr
    {
        if arr[index] == key {
            // Ensuring `counter` is within bounds before incrementation
            assert(counter < arr.len()); // This is conservatively assuming individual element counts cannot exceed total elements.
            counter += 1;
        }
        index += 1;
    }
    counter
}

// ...
}



//             counter += 1;
//   None: counter += 1

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False