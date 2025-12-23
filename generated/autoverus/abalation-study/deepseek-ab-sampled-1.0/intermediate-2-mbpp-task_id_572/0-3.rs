
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
    let mut index_counter = 0;
    let mut counter = 0;
    while (index_counter < arr.len())
        invariant
            index_counter <= arr.len(),
            counter == arr@.count(|x: i32| x == key && index_counter > x),
    {
        if (arr[index_counter] == key) {
            counter += 1;
        }
        index_counter += 1;
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
    while (index < arr.len())
        invariant
            index <= arr.len(),
            unique_arr.len() == arr@.take(index).filter(|x: i32| count_frequency_rcr(arr@, x) == 1).len(),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2