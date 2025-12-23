
#![verifier::loop_isolation(false)]
use vstd::math::*;
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

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

proof fn lemma_monotonic_max(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, i)) <= max_rcur(seq.subrange(0, j)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_max(seq, i, j - 1);
    }
}

proof fn lemma_monotonic_min(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, i)) >= min_rcur(seq.subrange(0, j)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_min(seq, i, j - 1);
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            1 <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2, // This invariant covers every element in the array and the array is never changed in the loop
            arr.len() == arr.len(),
            max_val as int - min_val as int <= i32::MAX as int,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        proof {
            lemma_seq_subrange_ascend(arr@, 0, ( index ) as int);
            lemma_monotonic_max(arr@, 0, ( index ) as int);
            lemma_monotonic_min(arr@, 0, ( index ) as int);
            assert(max_rcur(arr@.subrange(0, index as int)) >= min_rcur(arr@.subrange(0, index as int)));
            assert(max_rcur(arr@.subrange(0, index as int)) - min_rcur(arr@.subrange(0, index as int)) <= i32::MAX as int);
        }
    }

    // Assertion to ensure no overflow/underflow
    assert(max_val as int - min_val as int <= i32::MAX as int);
    assert(max_val as int - min_val as int >= i32::MIN as int);

    max_val - min_val
}

} // verus!





//             assert(max_rcur(arr@.subrange(0, index as int)) - min_rcur(arr@.subrange(0, index as int)) <= i32::MAX as int);
//   assertion failed: max_rcur(arr@.subrange(0, index as int)) - min_rcur(arr@.subrange(0, index as int)) <= i32::MAX as int

// Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 4
// Safe: True