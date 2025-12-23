
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

proof fn lemma_count_frequency_monotonicity(i: usize, j: usize)
    requires
        i <= j,
        j <= arr@.len(),
    ensures
        count_frequency_rcr(arr@.subrange(0, i as int), key) <= count_frequency_rcr(arr@.subrange(0, j as int), key),
{
    // Proof by induction on j - i
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index: usize = 0;
    let mut counter: usize = 0;
    while index < arr.len()
        invariant
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
    {
        if arr[index] == key {
            // Prove that counter + 1 will not cause an overflow
            assert!(counter <= usize::MAX - 1, "Arithmetic overflow in counter += 1");
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
    let input_len: usize = arr.len();
    let mut index: usize = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@.len() == index,
            unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False