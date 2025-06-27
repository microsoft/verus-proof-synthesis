
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

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            // max_val and min_val correctly represent the max and min values of arr[..index]
            forall|i: int| 0 <= i < index ==> max_val >= #[trigger] arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= #[trigger] arr[i],
            arr.len() > 0,
            arr.len() == arr.len(),
    {
        if arr[index] <= min_val {
            min_val = arr[index];
        } else if arr[index] > max_val {
            max_val = arr[index];
        }
        index += 1;
    }
    max_val + min_val
}

} // verus!

### Explanation
1. **Invariants**: Ensure invariants in the loop correctly express properties that should hold true at each iteration. The invariants ensure that `max_val` and `min_val` are the correct max and min of `arr[..index]`.

2. **Postcondition**: Ensures statement guarantees that the `sum` returned equals `max_rcur(arr@) + min_rcur(arr@)`.

### Running Verus
Make sure you run the Verus verification tool correctly. You should specify the single input file containing your code if you're encountering a "multiple input filenames" error.

For example, if you have a file named `main.rs`, you would run Verus as follows:

sh
verus main.rs

Or if using `cargo-verus`:

sh
cargo-verus run


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpg6c83dkv`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 16
// Safe: False