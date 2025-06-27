
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

proof fn lemma_monotonic(seq: Seq<i64>, i:nat, j:nat)
    requires
        i <= j,
        j <= seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, i as int)) <= sum_negative_to(seq.subrange(0, j as int)),
    decreases j - i
{
    if i < j {
        lemma_monotonic(seq, i, (j-1) as nat);
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;
    proof {
        assert(index < arr.len()); // Added by AI
    }
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(), // Upper bound copied from the function pre-condition
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
    {
        if (arr[index] < 0) {
            // Ensure no overflow/underflow occurs
            assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX) by {
                lemma_seq_subrange_ascend(arr@, 0, index as int + 1);
                lemma_seq_subrange_all(arr@);
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) <= sum_negative_to(arr@.subrange(0, arr.len() as int)));
                lemma_monotonic(arr@, (index + 1) as nat, arr.len() as nat);
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) <= i128::MAX);
            };
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!


//                 assert(sum_negative_to(arr@.subrange(0, index as int + 1)) <= i128::MAX);
//   assertion failed: sum_negative_to(arr@.subrange(0, index as int + 1)) <= i128::MAX

// Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 7
// Safe: True