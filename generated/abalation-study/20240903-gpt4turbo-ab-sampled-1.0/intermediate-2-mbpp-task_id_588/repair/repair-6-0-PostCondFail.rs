
#![verifier::loop_isolation(false)]
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
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < index ==> arr@[k as int] <= max_val,
            forall |k: int| 0 <= k < index ==> arr@[k as int] >= min_val,
            i32::MIN / 2 < min_val,
            max_val < i32::MAX / 2,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    proof {
        // Manual assertion replaced by auto-generated ghost variable and logic
        let ghost result_max = max_rcur(arr@);
        let ghost result_min = min_rcur(arr@);

        assert(max_val as int == result_max); // Correct is to assert against the ghost variable
        assert(min_val as int == result_min); 
    }
    max_val - min_val
}

} // verus!


// failed this postcondition
//         max_rcur(arr) == max_val as int,
// at the end of the function body
// {
//     // Hypothetical body; actual proof would require analyzing `max_rcur` and in-loop behavior.
// }
//   at the end of the function body: {     // Hypothetical body; actual proof would require analyzing `max_rcur` and in-loop behavior. }
//   failed this postcondition: max_rcur(arr) == max_val as int

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False