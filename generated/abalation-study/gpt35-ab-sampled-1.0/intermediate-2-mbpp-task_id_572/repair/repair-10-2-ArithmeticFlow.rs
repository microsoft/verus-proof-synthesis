
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

proof fn lemma_monotonic(i: int, j: int)
    requires
        i <= j,
    ensures
        count_frequency_rcr(arr@, i) <= count_frequency_rcr(arr@, j)
        decreases j - i
{
    if i < j {
        lemma_monotonic(i, j - 1);
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
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) == counter,
    {

        assert(count_frequency_rcr(arr@, arr[index]) <= counter + 1) by {
            lemma_monotonic(arr[index], arr[index]);
        }

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
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) <= 1,
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True