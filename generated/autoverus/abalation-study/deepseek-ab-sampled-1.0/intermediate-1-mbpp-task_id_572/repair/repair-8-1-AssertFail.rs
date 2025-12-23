

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

/// Prove that count_frequency matches count_frequency_rcr
proof fn count_frequency_correct(arr: &Vec<i32>, key: i32)
    ensures
        count_frequency(arr, key) as int == count_frequency_rcr(arr@, key),
{
    let freq = count_frequency(arr, key);
    assert(freq as int == count_frequency_rcr(arr@, key));
}

/// Prove that filtering based on frequency works as expected
proof fn filter_unique_elements(unique: Vec<i32>, arr: Vec<i32>)
    ensures
        unique@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    requires
        unique@.for_all(|x| count_frequency_rcr(arr@, x) == 1),
        unique@.no_duplicates(),
{
    // Show that all elements in unique are unique and meet the condition
    assert(forall |x| unique@.contains(x) ==> count_frequency_rcr(arr@, x) == 1);
    // Show that all elements in arr that meet the condition are in unique
    assert(forall |x| count_frequency_rcr(arr@, x) == 1 ==> unique@.contains(x));
    // Therefore, the two sets are equal
    assert(unique@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= counter <= index,
            counter <= arr.len(),
            index <= arr.len(),
            arr.len() == arr.len(), // Loop invariant for array length
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
    }
    proof {
        count_frequency_correct(arr, key);
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
            forall|j: int| 0 <= j < unique_arr.len() ==> count_frequency_rcr(arr@, unique_arr[j]) == 1,
            index <= arr.len(),
            unique_arr.len() <= index,
            unique_arr@.len() == unique_arr.len(),
            arr.len() == input_len,
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        filter_unique_elements(unique_arr, arr@);
    }
    unique_arr
}

} // verus!

//         assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
//   assertion failed: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False