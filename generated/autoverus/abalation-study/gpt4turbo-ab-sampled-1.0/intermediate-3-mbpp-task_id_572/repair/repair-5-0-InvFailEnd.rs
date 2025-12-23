
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
            index <= arr.len(),
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
            counter <= arr.len(), // Asserts that counter never exceeds arr.len., thus no overflow
    {
        if (arr[index] == key) {
            assert(counter < usize::MAX); // Ensures that adding 1 will not cause an overflow; could be domain-specifically bounded by arr.len() if necessary
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
    proof {
        reveal(count_frequency_rcr);
    }

    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    proof {
        assert(arr@ == arr@.subrange(0, arr.len() as int));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr.len() <= input_len,
            forall |k: int| 0 <= k < unique_arr.len() as int ==> unique_arr@[k] == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)[k],
            forall|k: int| 0 <= k < arr@.subrange(0, index as int).len() ==> count_frequency_rcr(arr@.subrange(0, index as int), arr@[k]) == count_frequency_rcr(arr@, arr@[k]),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
            proof {
                let f = || index;
                assert(by f, forall|k: int| 0 <= k < arr@.subrange(0, (index + 1) as int).len() ==> count_frequency_rcr(arr@.subrange(0, (index + 1) as int), arr@[k]) == count_frequency_rcr(arr@, arr@[k]));
            }
        }
        index += 1;
    }
    unique_arr
}

} // verus!


//             forall |k: int| 0 <= k < unique_arr.len() as int ==> unique_arr@[k] == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)[k],
//   None: forall |k: int| 0 <= k < unique_arr.len() as int ==> unique_arr@[k] == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1)[k]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False