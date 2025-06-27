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
    while index < arr.len()
        invariant
            forall|i: int| 0 <= i < index ==> (unique_arr@.contains(arr@[i]) ==> count_frequency_rcr(arr@, arr@[i]) == 1),
            forall|x: i32| unique_arr@.contains(x) ==> count_frequency_rcr(arr@, x) == 1,
            index <= arr.len(),
            unique_arr@.len() <= index,
    {
        if count_frequency(&arr, arr[index]) == 1 {
            proof {
                assert(count_frequency_rcr(arr@, arr@[( index ) as int]) == 1); // Added by AI
            }
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)); // Added by AI
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
//   at the end of the function body: {     let mut unique_arr: Vec<i32> = Vec::new();     let input_len = arr.len();     let mut index = 0;     while index < arr.len()         invariant             forall|i: int| 0 <= i < index ==> (unique_arr@.contains(arr@[i]) ==> count_frequency_rcr(arr@, arr@[i]) == 1),             forall|x: i32| unique_arr@.contains(x) ==> count_frequency_rcr(arr@, x) == 1,             index <= arr.len(),             unique_arr@.len() <= index,     {         if count_frequency(&arr, arr[index]) == 1 {             proof {                 assert(count_frequency_rcr(arr@, arr@[( index ) as int]) == 1); // Added by AI             }             unique_arr.push(arr[index]);         }         index += 1;     }     unique_arr }
//   failed this postcondition: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True