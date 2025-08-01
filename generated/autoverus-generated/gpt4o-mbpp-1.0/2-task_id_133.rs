
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

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

// Proof of monotonicity to ensure the bounds of expression
proof fn lemma_monotonic_sum_negatives(seq: Seq<i64>, n: nat)
    requires
        seq.len() >= n + 1 && n >= 0,
    ensures
        sum_negative_to(seq.subrange(0, n as int)) <= sum_negative_to(seq.subrange(0, (n+1) as int)),
{
    // To prove the monotonicity, we need to show that adding one more element that's negative
    // doesn't decrease the sum.
    if seq[( n ) as int] < 0 {
        assert(sum_negative_to(seq.subrange(0, n as int)) + seq[( n ) as int] as int == sum_negative_to(seq.subrange(0, (n+1) as int)));
    } else {
        assert(sum_negative_to(seq.subrange(0, n as int)) == sum_negative_to(seq.subrange(0, (n+1) as int)));
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            index <= arr.len(), // copied invariant
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // added this invariant because array `arr` is not modified in the loop
            forall |k: int|
                0 <= k < index as int ==>
                i128::MIN - arr[k] <= sum_neg, // Added by AI to ensure no underflow
            forall |k: int|
                0 <= k < arr.len() ==> arr[k] <= i128::MAX - sum_neg // Modified invariant to use arr[k] <= i128::MAX - sum_neg instead of i128::MIN - arr[k] <= sum_neg,
    {
        if (arr[index] < 0) {
            proof {
                assert(sum_neg as i128 + arr[( index ) as int] as i128 >= i128::MIN); // Check for underflow
            }
            assert(sum_neg as i128 + arr[( index ) as int] as i128 <= i128::MAX); // Check for overflow

            // Additional assertion for verification
            assert(sum_neg + (arr[( index ) as int] as i128) == sum_negative_to(arr@.subrange(0, index as int + 1)) as i128) by {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
                lemma_seq_subrange_all(arr@);
                lemma_monotonic_sum_negatives(arr@, index as nat);
            };

            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!

// Score: (3, 5)
// Safe: True