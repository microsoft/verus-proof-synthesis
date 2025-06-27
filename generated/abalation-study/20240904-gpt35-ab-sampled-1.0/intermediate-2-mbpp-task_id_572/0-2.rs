
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_count_frequency_rcr_base_case(seq: Seq<i32>, key: i32)
    requires
        seq.len() == 0,
    ensures
        count_frequency_rcr(seq, key) == 0,
{
    assert(count_frequency_rcr(seq, key) == 0);
}

proof fn lemma_count_frequency_rcr_recursive_case(seq: Seq<i32>, key: i32)
    requires
        seq.len() > 0,
    ensures
        count_frequency_rcr(seq, key) == count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) { 1 } else { 0 },
{
    assert(count_frequency_rcr(seq, key) == count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) { 1 } else { 0 });
}

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) { 1 as int } else { 0 as int }
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
            counter == count_frequency_rcr(arr[0..index].to_seq(), key),
    {
        if arr[index] == key {
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
            unique_arr@ == arr@[0..index].filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        if count_frequency(arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5