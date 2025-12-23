
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
    ghost let arr_len = arr.len();
    while index < arr_len
        invariant
            (forall|i: int| 0 <= i < index as int ==> arr[i as int] <= max_val),
            (forall|i: int| 0 <= i < index as int ==> arr[i as int] >= min_val),
            (forall|k: int|
                0 <= k < index ==> #[trigger] arr[k] <= max_val as i32 && #[trigger] arr[k] >= min_val as i32),
            0 <= index <= arr_len,
            index <= arr_len,
            index <= arr_len,
            min_val <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] <= max_val,
            forall|i: int| 0 <= i < index ==> arr[i] >= min_val,
    {
        assert(0 <= index < arr_len);
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        assert(index <= arr_len);
    }
    max_val - min_val
}

} // verus!


//             0 <= index < arr.len(),
//   None: index

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False