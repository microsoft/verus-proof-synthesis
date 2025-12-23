
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

proof fn lemma_diff_within_bounds(seq: Seq<i32>)
    ensures
        max_rcur(seq) - min_rcur(seq) >= 0,
{
    // This proof uses the monotonicity of max_rcur and min_rcur
    if seq.len() > 1 {
        let last = seq.last() as int;
        let max_rest = max_rcur(seq.drop_last());
        let min_rest = min_rcur(seq.drop_last());
        
        assert(last >= min_rest);
        assert(max_rest >= min_rest);
        
        if last >= max_rest {
            assert(max_rcur(seq) == last);
            assert(max_rcur(seq) - min_rcur(seq) == last - min(last, min_rest));
            assert(last >= min(last, min_rest));
        } else {
            assert(max_rcur(seq) == max_rest);
            assert(max_rcur(seq) - min_rcur(seq) == max(last, max_rest) - min_rest);
            assert(max_rest >= min_rest);
        }
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
    
    // Add the assertion to ensure bounds are respected
    assert(max_val as int - min_val as int >= 0) by {
        lemma_diff_within_bounds(arr@);
    };
    
    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: False