
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
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) == counter,
    {
        assert(counter + 1 >= counter) by {
            // Add a lemma to show that the counter is increasing monotonically
            // This is to ensure that counter + 1 won't cause an overflow
            lemma_counter_monotonic(counter, index as int);
        }
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
    }
    counter
}

proof fn lemma_counter_monotonic(c1: usize, c2: usize, i: usize)
    requires
        c1 <= c2,
        i <= arr.len(),
    ensures
        c1 <= c2+1,
{
    // Use underlying properties to prove that the counter is increasing monotonically
    // For example, if c1 <= c2 and current element is not the key, then c1 <= c2+1
    // This ensures that counter won't overflow
    // Add appropriate logic to prove this lemma
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
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) <= 1,
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