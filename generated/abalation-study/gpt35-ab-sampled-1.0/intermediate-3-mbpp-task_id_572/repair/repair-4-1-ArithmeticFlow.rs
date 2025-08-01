
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
proof fn lemma_counter_bound(arr: &Vec<i32>, key: i32, index: usize, counter: usize)
    requires
        count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
        index < arr.len(),
        counter < usize::MAX,  // Ensure counter doesn't overflow
        index + 1 <= arr.len(),  // Ensure index doesn't overflow
    ensures
        count_frequency_rcr(arr@.subrange(0, (index + 1) as int), key) == counter + if (arr[( index ) as int] == key) { 1 } else { 0 },
{
    // Add your implementation for the lemma function here
}

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
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
            index <= arr.len(),
    {
        assert(counter < usize::MAX) by {
            lemma_counter_bound(arr, key, index, counter);
        }
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
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
    {
        if count_frequency(&arr, arr[index]) == 1 {
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
// Safe: True