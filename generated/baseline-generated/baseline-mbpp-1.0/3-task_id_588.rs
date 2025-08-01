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

proof fn max_rcur_upper_bound(seq: Seq<i32>, upper_bound: int)
    requires
        seq.len() > 0,
        upper_bound >= max_rcur(seq),
    ensures
        upper_bound >= max_rcur(seq),
    decreases seq.len(),
{
    if seq.len() > 1 {
        max_rcur_upper_bound(seq.drop_last(), upper_bound);
    }
}

proof fn min_rcur_lower_bound(seq: Seq<i32>, lower_bound: int)
    requires
        seq.len() > 0,
        lower_bound <= min_rcur(seq),
    ensures
        lower_bound <= min_rcur(seq),
    decreases seq.len(),
{
    if seq.len() > 1 {
        min_rcur_lower_bound(seq.drop_last(), lower_bound);
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
            0 <= index <= arr.len(),
            max_val >= min_val,
            min_val <= min_rcur(arr@.take(index as int)),
            max_val >= max_rcur(arr@.take(index as int)),
    {
        if arr[index] <= min_val {
            min_val = arr[index];
            assert(min_val <= min_rcur(arr@.take((index + 1) as int))) by {
                min_rcur_lower_bound(arr@.take((index + 1) as int), min_val as int);
            }
        } else if arr[index] > max_val {
            max_val = arr[index];
            assert(max_val >= max_rcur(arr@.take((index + 1) as int))) by {
                max_rcur_upper_bound(arr@.take((index + 1) as int), max_val as int);
            }
        }
        index += 1;
    }
    max_val - min_val
}

} // verus!
// Score: (4, 2)
// Safe: False