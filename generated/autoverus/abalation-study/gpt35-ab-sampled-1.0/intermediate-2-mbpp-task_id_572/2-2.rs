
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1),
{
    assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
}

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
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
            index <= arr.len(),
            forall |j:int| 0 <= j < index ==> count_frequency_rcr(arr@.subrange(0, index as int), arr[j]) == counter,
    {
        if arr[index] == key {
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
            forall |j:int| 0 <= j < index ==> count_frequency(&arr, arr[j]) > 1,
            unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;

        proof {
            lemma_seq_subrange_ascend(arr@, 0, index as int);
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
    }

    unique_arr
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1