
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

proof fn lemma_non_negative_count(index: i32) 
    requires
        index >= 0,
    ensures
        count_frequency_rcr(arr@, arr[index]) >= 0,
{
    // Add proof for non-negativity of count_frequency_rcr
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    requires
        arr.len() as int == arr.len(),
    ensures
        count_frequency_rcr(arr@, key) as usize == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len() as int
        invariant
            0 <= index as usize <= arr.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) >= 0,
    {
        assert(counter + 1 >= 0) by {
            lemma_non_negative_count(index);
        }
        if (arr[index as usize] == key) {
            counter += 1;
        }
        index += 1;
    }
    counter as usize
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) as usize == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) as usize <= 1,
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False