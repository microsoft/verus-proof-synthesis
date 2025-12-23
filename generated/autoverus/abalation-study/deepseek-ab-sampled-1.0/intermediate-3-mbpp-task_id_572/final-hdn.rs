

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

proof fn lemma_monotonic_cfr(j: int, seq: Seq<i32>, key: i32)
    requires
        j <= seq.len(),
    ensures
        count_frequency_rcr(seq.subrange(0, j), key) <= count_frequency_rcr(seq, key),
    decreases seq.len()
{
    if j < seq.len() {
        lemma_monotonic_cfr(j, seq.drop_last(), key);
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
            counter <= arr.len(),
            index <= arr.len(),
    {
        if (arr[index] == key) {
                lemma_monotonic_cfr(counter as int, arr@.subrange(0, index as int), key);
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
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    let ghost _ = (); // Added by AI

    proof {
        // Verify that for the initial state, the invariant holds.
        assert(unique_arr@ == arr@.subrange(0, 0).filter(|x| count_frequency_rcr(arr@, x) == 1));
        assert(arr@.subrange(0, 0).filter(|x| count_frequency_rcr(arr@, x) == 1).len() == 0);
        assert(unique_arr@.len() == 0);
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
        proof {
        }
    }
    unique_arr
}

} // verus!

// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1