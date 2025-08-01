
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
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
    {
        if (arr[index] == key) {
            // Ensure that adding 1 will not cause overflow
            assert!(counter <= arr.len() - 1, "Counter about to overflow");
            counter += 1;
        }
        index += 1;
    }
    counter
}

proof fn lemma_monotonic(i: nat, j: nat, key: i32, seq: Seq<i32>)
    requires
        i <= j,
        count_frequency_rcr(seq@.subrange(0, i as int), key) == i,
    ensures
        count_frequency_rcr(seq@.subrange(0, j as int), key) >= i,
{
    // Since i <= j, the count in the longer sequence can't be less than the shorter
    for (let k = i as int; k < j as int; k += 1) {
        count_frequency_rcr(seq@.subrange(0, k as int), key) <=
            count_frequency_rcr(seq@.subrange(0, (k + 1) as int), key);
    }
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_ar: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < input_len
        invariant
            index <= input_len,
            unique_ar@.len() == index,
            unique_ar@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
    {
        if count_frequency(arr, arr[index]) == 1 {
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