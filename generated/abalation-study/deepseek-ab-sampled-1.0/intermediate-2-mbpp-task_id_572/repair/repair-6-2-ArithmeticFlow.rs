
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

// Lemma function to prove the non-negativity and boundedness of count_frequency_rcr
lemma! { pub lemma_count_frequency_non_negative(seq: Seq<i32>, key: i32) -> ()
    ensures count_frequency_rcr(seq, key) >= 0,
{
    use_cases!()
}

lemma! { pub lemma_count_frequency_boundedAbove(seq: Seq<i32>, key: i32) -> ()
    ensures count_frequency_rcr(seq, key) <= seq.len() as int,
{
    use_cases!()
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
            // Assertion to prove the value is within bounds
            assert!(count_frequency_rcr(arr@.subrange(0, index as int + 1), key) <= arr.len() as int) by {
                lemma_count_frequency_boundedAbove(arr@.subrange(0, index as int + 1), key);
            };
            assert!(count_frequency_rcr(arr@.subrange(0, index as int + 1), key) >= 0) by {
                lemma_count_frequency_non_negative(arr@.subrange(0, index as int + 1), key);
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

} // verus!


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False