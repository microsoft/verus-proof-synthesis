
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

proof fn lemma_non_negative_counter(counter: int)
    requires
        counter >= 0,
    ensures
        counter + 1 > 0,
{
    // Prove that if counter is non-negative, then counter + 1 is positive
    // This lemma is used to assert the bound of counter += 1
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
            forall|j: int| 0 <= j < index ==> count_frequency_rcr(arr@, arr[j]) == counter,
    {
        if (arr[index] == key) {
            assert(counter >= 0) by {
                lemma_non_negative_counter(( counter ) as int);
            }
            counter += 1; // Assertion about the bound of counter += 1 added here
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
            0 <= index <= arr.len(),
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



//             counter += 1; // Assertion about the bound of counter += 1 added here
//   None: counter += 1

// Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 6
// Safe: True