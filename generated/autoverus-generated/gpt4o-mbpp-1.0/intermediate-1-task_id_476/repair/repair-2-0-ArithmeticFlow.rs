
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

proof fn lemma_monotonic_bounds(seq: Seq<i32>)
    requires
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        max_rcur(seq) + min_rcur(seq) < i32::MAX,
        max_rcur(seq) + min_rcur(seq) > i32::MIN,
{
    // We can prove this by induction on the length of the sequence.
    // Base case: When sequence has length 1.
    if seq.len() == 1 {
        assert(seq.first() as int + seq.first() as int < i32::MAX);
        assert(seq.first() as int + seq.first() as int > i32::MIN);
    } else {
        // Inductive case: Use the properties of max and min to show the bounds
        assert(max_rcur(seq) <= seq[seq.len() - 1] as int || max_rcur(seq) == max_rcur(seq.drop_last()));
        assert(min_rcur(seq) >= seq[seq.len() - 1] as int || min_rcur(seq) == min_rcur(seq.drop_last()));
        lemma_monotonic_bounds(seq.drop_last());
    }
}

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            1 <= index <= arr.len(),
            arr.len() > 0,
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
            forall|i: int| 0 <= i < index ==> min_val <= # [trigger] arr[i] <= max_val,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    assert(max_val as int + min_val as int < i32::MAX as int && max_val as int + min_val as int > i32::MIN as int) by {
        lemma_monotonic_bounds(arr@);
    };
    
    max_val + min_val
}

} // verus!


//     max_val + min_val
//   None: max_val + min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False