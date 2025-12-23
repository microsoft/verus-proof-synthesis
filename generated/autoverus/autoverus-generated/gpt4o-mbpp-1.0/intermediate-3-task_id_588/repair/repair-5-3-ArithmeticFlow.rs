
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;
fn main() {}
verus! {

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

proof fn lemma_monotonicity(seq: Seq<i32>, i: nat, j: nat)
    requires
        i <= j < seq.len(),
    ensures
        min_rcur(seq.subrange(0, i as int)) >= min_rcur(seq.subrange(0, j as int)) &&
        max_rcur(seq.subrange(0, i as int)) <= max_rcur(seq.subrange(0, j as int)),
    decreases j
{
    // Proof of the monotonicity of max_rcur and min_rcur as sequence increases
    if i < j {
        lemma_monotonicity(seq, i, (j - 1) as nat);
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2, // Added invariant to cover every element of arr, assuming arr is not modified in the loop
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }
    
    // Assertion about bounds before computing difference
    assert(max_val >= min_val) by {
        lemma_monotonicity(arr@, 0, ( arr.len() as nat - 1 ) as nat);
    }

    // Compute the difference
    max_val - min_val
}

} // verus!



//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: False