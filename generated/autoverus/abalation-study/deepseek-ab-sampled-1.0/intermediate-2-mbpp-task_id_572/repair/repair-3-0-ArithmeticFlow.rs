
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
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

// Monotonicity Lemma
proof fn lemma_monotonicity(i: int)
    requires
        i >= 0,
        count_frequency_rcr(Seq::new(), arr@.index(0 as int)), key) <= count_frequency_rcr(Seq::new() + arr@, key),
    ensures
        count_frequency_rcr(Seq::new() + arr@.drop_last(i as nat).elements(), key) <=
        count_frequency_rcr(Seq::new() + arr@.elements(), key),
    decreases i
{
    if i > 0 {
        lemma_monotonicity(i - 1);
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
            // Assertion to prevent overflow
            assert(counter + 1 <= count_frequency_rcr(arr@.subrange(0, index.as_nat() + 1), key)) by {
                lemma_monotonicity(index as int);
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
    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@.len() == index,
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

// verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False