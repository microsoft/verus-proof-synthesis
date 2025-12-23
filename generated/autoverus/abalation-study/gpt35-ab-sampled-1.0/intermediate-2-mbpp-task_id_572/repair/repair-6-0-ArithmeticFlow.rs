
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

proof fn lemma_monotonic_count_frequency(index: int, k: int, arr: Seq<i32>, key: int)
    requires
        0 <= k < index,
    ensures
        count_frequency_rcr(arr[( ..index + 1 ) as int], key) == count_frequency_rcr(arr[..index], key) + if (arr[index] == key) {
            1 as int
        } else {
            0 as int
        },
    decreases index - k
{
    if index > k {
        lemma_monotonic_count_frequency(index - 1, k, arr, key);
    }
}

fn count_frequency(arr: &Seq<i32>, key: i32) -> (frequency: usize)
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
        assert(counter + (arr[index] == key) as usize <= count_frequency_rcr(arr@, key)) by {
            lemma_monotonic_count_frequency(index as int, 0, arr@, key);
        }
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
    }
    counter
}

fn remove_duplicates(arr: &Seq<i32>) -> (unique_arr: Seq<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Seq<i32> = Seq::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|k: int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) <= 1,
    {
        if count_frequency(arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!



//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 21
// Safe: False