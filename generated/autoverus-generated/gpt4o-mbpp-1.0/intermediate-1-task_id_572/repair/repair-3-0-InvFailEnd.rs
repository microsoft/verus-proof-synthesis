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
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter as int,
            index <= arr.len(),
            arr.len() == arr.len(),
    {
        if (arr[index] == key) {
            // Add bounds check assertion here
            assert(counter < usize::MAX) by {
                // If counter is at max, incrementing it will overflow
                // But considering arr.len() is at max usize, we ensure counter won't reach usize::MAX
                // since it's bounded by the length of arr.
                assert(arr.len() < usize::MAX);
                assert(counter <= arr.len());
            };
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
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    proof {
        assert(unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
        assert(forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k]);
    } // Added by AI
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
            forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k], // Invariant covers entire array because `arr` is never modified in the loop.
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;

        proof {
            assert(unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
        } // Added by AI
    }
    unique_arr
}

} // verus!

//             unique_arr@ == arr@.subrange(0, index as int).filter(
//                 |x: i32| count_frequency_rcr(arr@, x) == 1,
//             ),
//   None: unique_arr@ == arr@.subrange(0, index as int).filter(                 |x: i32| count_frequency_rcr(arr@, x) == 1,             )

// Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 6
// Safe: True