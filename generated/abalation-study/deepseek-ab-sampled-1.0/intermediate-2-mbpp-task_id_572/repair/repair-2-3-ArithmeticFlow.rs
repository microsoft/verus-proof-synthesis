
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
            index <= arr.len(),
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
    {
        if arr[index] == key {
            // Ensure that adding 1 to counter does not cause overflow
            assert!(counter + 1 <= count_frequency_rcr(arr@, key)) by {
                // Use the lemma to show the correctness of the increment
            };
            counter += 1;
        }
        index += 1;
    }
    counter
}

// Lemma proof showing that the increment is valid
proof fn lemma_counter_invariant(index: usize, arr: &Vec<i32>, key: i32)
    requires
        index <= arr.len(),
        count_frequency_rcr(arr@.subrange(0, index as int), key) <= count_frequency_rcr(arr@, key),
    ensures
        count_frequency_rcr(arr@.subrange(0, index as int), key) + 1 <= count_frequency_rcr(arr@, key) if (arr[index] == key),
{
    // Implementation of the proof goes here
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@.len() == index,
            unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        if count_frequency(arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False