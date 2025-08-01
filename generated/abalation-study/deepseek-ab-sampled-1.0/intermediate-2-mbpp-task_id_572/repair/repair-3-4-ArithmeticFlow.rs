
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
    {
        if (arr[index] == key) {
            // Assertion to ensure counter + 1 doesn't overflow
            if counter + 1 > arr.len() as usize {
                abort();
            }
            
            // Ensure the count remains within 0..=arr.len()
            assert(counter + 1 <= arr.len() as usize) by {
                // Use the recursive spec to prove the upper bound
                let cnt = count_frequency_rcr(arr@.subrange(0, (index + 1) as int), key);
                cnt <= count_frequency_rcr(arr@.subrange(0, index as int), key) + 1;
                cnt >= 0;
                cnt <= arr.len() as usize;
                counter + 1 <= arr.len() as usize;
            };
            
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False