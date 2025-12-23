
use vstd::prelude::*;
fn main() {}
verus! {

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
    {
        if (arr[index] < 0) {
            assert(sum_neg as i128 + arr[( index ) as int] as i128 >= i128::MIN); // Check for underflow
            assert(sum_neg as i128 + arr[( index ) as int] as i128 <= i128::MAX); // Check for overflow

            // Additional assertion for verification
            assert(sum_neg + (arr[( index ) as int] as i128) == sum_negative_to(arr@.subrange(0, index as int + 1)) as i128) by {
                lemma_monotonic_sum_negatives(arr@, index as nat);
            };

            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!







//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: True