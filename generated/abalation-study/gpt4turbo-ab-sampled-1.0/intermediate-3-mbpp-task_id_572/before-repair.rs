
use vstd::prelude::*;

fn main() {}

verus! {

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
            // arr.len() is never changed in the loop, represents invariance of array size
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    proof {
        reveal(count_frequency_rcr);
    }

    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    proof {
        assert(arr@ == arr@.subrange(0, arr.len() as int));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            // No set operation on unique_arr within the loop, thus its content is never changed.
            unique_arr.len() <= input_len, // Reflects the fact that unique_arr can't have more elements than arr
            forall |k: int| 0 <= k < unique_arr.len() as int ==> unique_arr@[k] == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)[k], // Added to cover every element in unique_arr
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 6