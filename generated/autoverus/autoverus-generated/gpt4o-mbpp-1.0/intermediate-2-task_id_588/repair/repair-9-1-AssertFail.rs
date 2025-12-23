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

proof fn min_rcur_is_min(arr: Seq<i32>, min_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> min_val <= arr[i],
        exists|i: int| 0 <= i < arr.len() && arr[i] == min_val,
    ensures
        min_rcur(arr) == min_val as int,
{
    if arr.len() == 1 {
        assert(arr.first() == min_val);
        assert(min_rcur(arr) == arr.first() as int);
    } else {
        let last = arr.last();
        let rest = arr.drop_last();
        if last < min_val {
            assert(false); // This branch should be impossible
        } else {
            min_rcur_is_min(rest, min_val);
            assert(min_rcur(arr) == min_rcur(rest).min(last as int));
        }
    }
}

proof fn max_rcur_is_max(arr: Seq<i32>, max_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max_val,
        exists|i: int| 0 <= i < arr.len() && arr[i] == max_val,
    ensures
        max_rcur(arr) == max_val as int,
{
    if arr.len() == 1 {
        assert(arr.first() == max_val);
        assert(max_rcur(arr) == arr.first() as int);
    } else {
        let last = arr.last();
        let rest = arr.drop_last();
        if last > max_val {
            assert(false); // This branch should be impossible
        } else {
            max_rcur_is_max(rest, max_val);
            assert(max_rcur(arr) == max_rcur(rest).max(last as int));
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

    // Assertion to ensure the invariants hold before the loop
    assert(0 <= 0 < arr.len());
    assert(max_val >= arr[0] && min_val <= arr[0]);

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            1 <= arr.len(),
            exists|i: int| 0 <= i < index && max_val == arr[i],
            exists|i: int| 0 <= i < index && min_val == arr[i],
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            forall|i: int| 0 <= i < index ==> max_val >= arr[i], // Updated invariant to cover elements up to index
            forall|i: int| 0 <= i < index ==> min_val <= arr[i], // Updated invariant to cover elements up to index
            min_val <= max_val,
            arr.len() == arr.len(), // Added invariant specifying the length of the array
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    proof {
        assert(forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i]); // Added by AI, for assertion fail
        assert(forall|i: int| 0 <= i < arr.len() ==> min_val <= arr[i]); // Added by AI, for assertion fail
        max_rcur_is_max(arr@, max_val); // Added by AI, for assertion fail
        min_rcur_is_min(arr@, min_val); // Added by AI, for assertion fail
        assert(max_rcur(arr@) == max_val as int);
        assert(min_rcur(arr@) == min_val as int);
    }
    
    max_val - min_val
}

}

//         assert(min_rcur(arr@) == min_val as int);
//   assertion failed: min_rcur(arr@) == min_val as int

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True