
use vstd::prelude::*;

fn main() {}

verus! {

// Spec function remains unchanged.
pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if seq.last() == key {
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
            index <= arr.len(),
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter as int,
    {
        if arr[index] == key {
            // Assert that before incrementing, counter is less than the array's length (safe boundary)
            assert(counter < usize::MAX); // General safeguard against overflow (though somewhat superficial given variable types and Rust's checks)
            assert(counter as int < count_frequency_rcr(arr@, key)); // Ensure the counter is within bounds defined by our spec function
            counter += 1;
        }
        index += 1;
    }
    counter
}

// Other functions remain unchanged.

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False