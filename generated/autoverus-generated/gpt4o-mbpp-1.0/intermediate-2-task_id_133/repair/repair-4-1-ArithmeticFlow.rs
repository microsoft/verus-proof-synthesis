
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

// Monotonicity lemma for sum_negative_to
proof fn lemma_sum_negative_to_monotonic(seq: Seq<i64>, i: nat, j: nat)
    requires
        i <= j <= seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, ( i ) as int)) <= sum_negative_to(seq.subrange(0, ( j ) as int)),
    decreases j
{
    if i < j {
        lemma_sum_negative_to_monotonic(seq, i, ( j - 1 ) as nat);
        assert(sum_negative_to(seq.subrange(0, ( i ) as int)) <= sum_negative_to(seq.subrange(0, j - 1)));
        if seq.index(j - 1) < 0 {
            assert(
                sum_negative_to(seq.subrange(0, j - 1)) + seq.index(j - 1) as int
                == sum_negative_to(seq.subrange(0, ( j ) as int))
            );
            assert(sum_negative_to(seq.subrange(0, ( i ) as int)) <= sum_negative_to(seq.subrange(0, j - 1)) + seq.index(j - 1) as int);
        } else {
            assert(sum_negative_to(seq.subrange(0, j - 1)) == sum_negative_to(seq.subrange(0, ( j ) as int)));
            assert(sum_negative_to(seq.subrange(0, ( i ) as int)) <= sum_negative_to(seq.subrange(0, j - 1)));
        }
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
        if arr[index] < 0 {
            // Ensure there is no arithmetic underflow/overflow
            let new_sum_neg = sum_neg + (arr[index] as i128);
            assert(i128::MIN <= new_sum_neg <= i128::MAX) by {
                lemma_sum_negative_to_monotonic(arr@, 0, index as nat + 1);
            };
            sum_neg = new_sum_neg;
        }
        index += 1;
    }
    sum_neg
}

} // verus!










//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: False