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
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
            index <= arr.len(),
    {
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
    while index < input_len  // Corrected the loop condition to check against `input_len` not changing.
        invariant
            forall|i: int| 0 <= i < unique_arr@.len() ==> unique_arr@.contains(arr@[i]), // Corrected assertion.
            index <= input_len,
            unique_arr@.len() <= index,
            forall|i: int| 0 <= i < index ==> unique_arr@.contains(arr@[i]) ==> count_frequency_rcr(arr@, arr@[i]) == 1,
            forall|k: int| 0 <= k < arr@.len() ==> count_frequency_rcr(arr@, arr@[k]) == 1 ==> unique_arr@.contains(arr@[k]) || k >= index,
    {
        if count_frequency(arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }

    proof {
        assert!(forall|i: int| 0 <= i < arr@.len() ==> count_frequency_rcr(arr@, arr@[i]) == 1 ==> unique_arr@.contains(arr@[i]));
    }

    unique_arr
}

} // verus!

// failed this postcondition
//         unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
// at the end of the function body
// {
//     let mut unique_arr: Vec<i32> = Vec::new();
//     let input_len = arr.len();
//     let mut index = 0;
// ...
//     unique_arr
// }
//   at the end of the function body: {     let mut unique_arr: Vec<i32> = Vec::new();     let input_len = arr.len();     let mut index = 0;     while index < arr.len()         invariant             forall|i: int| 0 <= i < unique_arr@.len() ==> arr@.contains(unique_arr@[i]), // Corrected assertion.             index <= arr.len(),             unique_arr@.len() <= index,     {         if count_frequency(&arr, arr[index]) == 1 {             unique_arr.push(arr[index]);         }         index += 1;     }     unique_arr }
//   failed this postcondition: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False