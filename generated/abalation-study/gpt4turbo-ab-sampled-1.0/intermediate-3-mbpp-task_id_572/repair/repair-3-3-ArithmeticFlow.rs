
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
        count_frequency_rcr(arr@, key) == frequency as int,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter as int,
    {
        if (arr[index] == key) {
            // Assert that counter can safely be incremented without overflow
            assert(counter < usize::MAX);
            counter += 1;
        }
        index += 1;
    }
    counter
}

// ... rest of the code ...

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False