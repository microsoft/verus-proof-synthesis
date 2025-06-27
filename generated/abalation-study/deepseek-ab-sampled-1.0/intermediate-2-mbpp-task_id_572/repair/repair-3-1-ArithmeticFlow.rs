
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

proof fn lemma_monotonic_frequency(i: int, j: int)
    requires
        i <= j,
    ensures
        count_frequency_rcr(arr@.subrange(0, i), key) <= count_frequency_rcr(arr@.subrange(0, j), key),
{
    if i < j {
        lemma_monotonic_frequency(i, j - 1);
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
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
    {
        if (arr[index] == key) {
            assert!(counter + 1 <= count_frequency_rcr(arr@, key)) by {
                lemma_monotonic_frequency(index as int, arr.len() as int);
            };
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
    let mut unique_ar: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_ar@.len() == index,
            unique_ar@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            assert!(counter + 1 <= count_frequency_rcr(arr@, key)) by {
                lemma_monotonic_frequency(index as int, arr.len() as int);
            };
            unique_ar.push(arr[index]);
        }
        index += 1;
    }
    unique_ar
}

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False