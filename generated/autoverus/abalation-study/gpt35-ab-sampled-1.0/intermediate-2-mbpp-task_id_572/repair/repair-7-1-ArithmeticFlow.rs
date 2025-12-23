
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

proof fn lemma_monotonic_count_frequency(index: u64, arr: &Vec<i32>, key: i32, counter: usize)
    requires
        count_frequency_rcr(arr@, key) <= counter,
    ensures
        count_frequency(&arr, key) <= counter,
{
    assert(count_frequency_rcr(arr@, arr[index as int]) <= counter) by {
        lemma_monotonic_count_frequency(( index + 1 ) as u64, arr, key, counter);
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index: u64 = 0;
    let mut counter: usize = 0;
    while index < arr.len() as u64
        invariant
            0 <= index <= arr.len() as u64,
            forall|k: int| 0 <= k < index as int ==> count_frequency_rcr(arr@, arr[k as int]) == counter,
    {
        assert(count_frequency_rcr(arr@, key) <= counter) by {
            lemma_monotonic_count_frequency(index, arr, key, counter);
        }
        if (arr[index as usize] == key) {
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
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) <= 1,
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