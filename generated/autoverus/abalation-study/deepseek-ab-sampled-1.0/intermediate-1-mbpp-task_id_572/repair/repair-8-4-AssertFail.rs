
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

proof fn count_frequency_rcr_correctness(seq: Seq<i32>, key: i32)
    ensures
        count_frequency_rcr(seq, key) == count_frequency(seq, key) as int,
{
    induction seq with {
        case Seq::empty() => {},
        case Seq::push front seq' => {
            proof {
                count_frequency_rcr_correctness(seq', key);
            }
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
            counter <= arr.len(),
            index <= arr.len(),
            arr.len() == arr.len(), // Loop invariant for array length
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
            forall|j: int| 0 <= j < unique_arr.len() ==> count_frequency_rcr(arr@, unique_arr[j]) == 1,
            index <= arr.len(),
            unique_arr.len() <= index,
            unique_arr@.len() == unique_arr.len(),
            arr.len() == input_len,
    {
        let freq = count_frequency(&arr, arr[index]);
        if freq == 1 as usize {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    proof {
        let val = arr@[index as int];
        assert(count_frequency_rcr(arr@, val) == if count_frequency(arr, val) == 1 as usize { 1 as int } else { 0 as int });
        assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    unique_arr
}

} // verus!


//         assert(unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
//   assertion failed: unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False