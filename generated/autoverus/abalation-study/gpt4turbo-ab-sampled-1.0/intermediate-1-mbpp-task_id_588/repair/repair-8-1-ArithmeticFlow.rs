
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

proof fn lemma_difference_within_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < # [trigger] seq[i] < i32::MAX / 2,
    ensures
        max_rcur(seq) - min_rcur(seq) <= i32::MAX / 2,
{
    // The body of this lemma will provide a mathematical proof that, given the constraints,
    // the difference between the maximum recursive and minimum recursive values
    // of any sequence of i32 integers within the specified bounds will not exceed i32::MAX / 2.
    // This might involve demonstrating, via inductive reasoning, that the properties of max_rcur
    // and min_rcur inherently maintain this difference within bounds.
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
            1 <= index,
            arr.len() > 0,
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            index <= arr.len(),
            max_val - min_val <= i32::MAX / 2, // Strengthened invariant
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    lemma_difference_within_bounds(arr@); // Assure the bounds before the subtraction
    assert(max_val - min_val <= i32::MAX / 2); // Explicit assurance might be redundant but adds clarity
    max_val - min_val
}

}


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False