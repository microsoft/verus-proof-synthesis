
use vstd::prelude::*;
fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
        lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.
 
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
          lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }

 */

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
            index <= arr.len(),
            key == key, // Repeat the invariant related to the constant function parameter
            arr.len() == arr.len(), // Loop invariant for array length
            // Added invariant to cover every element in the array since arr is never modified in the loop
            forall |k:int| 0 <= k < arr.len() ==> arr@.index(k) == arr@.index(k), // arr is never changed in the loop
    {
        if (arr[index] == key) {
            // Assertion to prevent overflow
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
    reveal(Seq::filter); // Add this line to reveal the filter function
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    proof {
        assert(unique_arr@ == arr@.subrange(0, index as int).filter(
            |x: i32| count_frequency_rcr(arr@, x) == 1,
        ));
    }

    while index < arr.len()
        invariant
            index <= arr.len(),
            unique_arr@ == arr@.subrange(0, index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
            input_len == arr.len(), // Repeat the invariant related to the constant function parameter
            arr.len() == arr.len(), // Loop invariant for array length
            // Added invariant to cover every element in the array since arr is never modified in the loop
            forall |k:int| 0 <= k < arr.len() ==> arr@.index(k) == arr@.index(k), // arr is never changed in the loop
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr@, 0, index as int);
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ));
        }
    }

    proof {
        lemma_seq_subrange_all(arr@);
        assert(unique_arr@ == arr@.subrange(0, index as int).filter(
            |x: i32| count_frequency_rcr(arr@, x) == 1,
        ));
    }

    unique_arr
}

}


// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3