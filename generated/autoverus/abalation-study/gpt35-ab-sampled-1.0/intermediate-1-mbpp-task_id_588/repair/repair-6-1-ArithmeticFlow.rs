
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

proof fn lemma_monotonic_max_min(arr: &Vec<i32>, i: nat, j: nat)
    requires
        i <= j,
    ensures
        min_rcur(arr.slice(0..(j as usize))) <= min_rcur(arr.slice(0..(i as usize))),
        max_rcur(arr.slice(0..(i as usize))) <= max_rcur(arr.slice(0..(j as usize))),
    decreases j
{
    if i < j {
        lemma_monotonic_max_min(arr, i, (j-1) as nat);
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2, // Fixed by AI
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;

    assert(max_val >= min_val) by {
        lemma_monotonic_max_min(arr, 0, arr.len() as nat);
    }

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            i32::MIN / 2 <= max_val && max_val <= i32::MAX / 2, // Fixed by AI
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True