
use vstd::prelude::*;
fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
        lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

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
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
            counter >= 0,
            index <= arr.len(),
            arr.len() == arr.len(), // arr is never modified in the loop
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k],
    {
        if (arr[index] == key) {
            // Add assertion to ensure counter does not overflow
            assert(counter < usize::MAX);
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
    // Reveal the implementation of Seq::filter
    reveal(Seq::filter);
    
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|i: int| 0 <= i < index ==> (arr[i] == arr@.index(i)),
            forall|i: int|
                0 <= i < unique_arr.len() ==> count_frequency_rcr(arr@, unique_arr[i]) == 1,
            index <= arr.len(),
            unique_arr.len() <= index,
            arr.len() == arr.len(), // arr is never modified in the loop
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k],
            unique_arr.len() == unique_arr.len(),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        lemma_seq_subrange_all(arr@);
        lemma_seq_subrange_all(unique_arr@);
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    unique_arr
}

} // verus!


//         assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
//   assertion failed: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 4
// Safe: True