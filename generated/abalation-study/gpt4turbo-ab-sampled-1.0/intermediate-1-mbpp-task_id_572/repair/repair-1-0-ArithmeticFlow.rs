
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
            1
        } else {
            0
        }
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency as int,
{
    let mut index = 0;
    let mut counter = 0;
    
    while index < arr.len()
        invariant
            counter as int == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
            arr.len() == arr.len(), // Ensures loop invariant maintains array length
    {
        if (arr[index] == key) {
            // Ensure we do not exceed maximum occurrences before incrementing
            assert(counter < arr.len()); // Asserting logical bounds before increment
            counter += 1;
        }
        index += 1;
    }
    counter
}

// remove_duplicates function remains unchanged

}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False