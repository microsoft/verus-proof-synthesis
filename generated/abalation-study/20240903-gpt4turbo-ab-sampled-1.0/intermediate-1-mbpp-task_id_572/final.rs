
use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

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
            counter <= arr.len(),
            counter == count_frequency_rcr(arr@.subrange(0, index as int), key),
            index <= arr.len(),
            arr.len() == arr.len(),
    {
        if (arr[index] == key) {
            assert(counter < arr.len());
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
    proof {
        reveal(Seq::filter);
        assert(unique_arr@ == arr@.subrange(0, 0).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));
    }
    while index < arr.len()
        invariant
            index <= arr.len(),
            arr.len() == arr.len(),
            unique_arr.len() == unique_arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr@, 0, ( index + 1 ) as int);             
            lemma_seq_subrange_all(arr@);   
            // Added assertion to satisfy the invariant directly at the end of the loop
            assert(unique_arr@ == arr@.subrange(0, index as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1));          
        }
    }
    unique_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 6