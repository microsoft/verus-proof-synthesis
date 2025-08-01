
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_monotonic_count_frequency_rcr(seq: Seq<i32>, key: i32, i: nat, j: nat)
    requires
        i <= j,
    ensures
        count_frequency_rcr(seq, key, i) <= count_frequency_rcr(seq, key, j),
    decreases j - i
{
    if i < j {
        lemma_monotonic_count_frequency_rcr(seq, key, i, ( j - 1 ) as nat);
    }
}

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32, index: nat) -> int
    decreases seq.len() - index
{
    if index == seq.len() {
        0
    } else if seq[( index ) as int] == key {
        1 + count_frequency_rcr(seq, key, index + 1)
    } else {
        count_frequency_rcr(seq, key, index + 1)
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key, 0) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            count_frequency_rcr(arr@, key, 0) == counter,
            index <= arr.len(),
    {
        if (arr[index] == key) {
            assert(counter + 1 > counter) by {
                lemma_monotonic_count_frequency_rcr(arr@, key, index as nat, arr.len() as nat);
            }
            counter += 1;
        }
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x, 0) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!




//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False