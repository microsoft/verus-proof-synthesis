
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_filter_compose<T>(v: Seq<T>, p: impl Fn(T) -> bool, q: impl Fn(T) -> bool)
    ensures
        v.filter(|x| p(x) && q(x)) == v.filter(( p ) as FnSpec<(T,), bool>).filter(q),
{
    assert(v.filter(|x| p(x) && q(x)) =~= v.filter(p).filter(q));
}

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
            0 <= index <= arr.len(),
            counter == count_frequency_rcr(arr@.take(index), key),
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
    proof {
        reveal(lemma_seq_filter_compose);
    }
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall |k:int| 0 <= k < index ==> count_frequency_rcr(arr@, arr[k]) == 1,
            unique_arr.len() == count_frequency_rcr(arr@.take(index), arr[index]),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
    }
    unique_arr
}

} // verus!


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1