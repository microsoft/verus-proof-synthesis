
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
        let n = arr.len();
        let mut min_val = arr[0];
        let mut max_val = arr[0];
        let mut index = 1;
        while index < n
            invariant
                1 <= index <= n,
                forall|i: int| 0 <= i < n ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
                // arr is never changed in the loop:
                forall|i: int| 0 <= i < index ==> max_val >= #[trigger] arr[i],
                // arr is never changed in the loop:
                forall|i: int| 0 <= i < index ==> min_val <= #[trigger] arr[i],
                n > 0,
                n == arr.len(), // Added by AI: directly using `n`
                // additional invariant about sum:
                exists|r_max: Seq<int>, r_min: Seq<int>| is_reorder_of(r_max, arr@.take(index as int), arr@) && is_reorder_of(r_min, arr@.take(index as int), arr@) &&
                max_rcur(arr@.take(index as int)) == max_val && min_rcur(arr@.take(index as int)) == min_val
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

    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps4k2ul9j`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3
// Safe: False