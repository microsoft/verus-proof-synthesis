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

proof fn lemma_max_min_monotonic(seq: Seq<i32>, i: int, j:int)
    requires
        0 <= i < j <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, i)) <= min_rcur(seq.subrange(0, j)) <= max_rcur(seq.subrange(0, j)) <= max_rcur(seq.subrange(0, ( seq.len() ) as int)),
        min_rcur(seq.subrange(0, i)) <= max_rcur(seq.subrange(0, j)),
    decreases j - i
{
    if i + 1 < j {
        lemma_max_min_monotonic(seq, i + 1, j);
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
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, index as int)),
            min_val == min_rcur(arr@.subrange(0, index as int)),
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < # [trigger] arr[k] < i32::MAX / 2,
            max_val as int - min_val as int <= i32::MAX as int, // Added by AI, for assertion fail
            max_val as int - min_val as int >= i32::MIN as int, // Added by AI, for assertion fail
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;

        proof {
            assert(max_val as int - min_val as int <= i32::MAX as int); // Added by AI
            assert(max_val as int - min_val as int >= i32::MIN as int); // Added by AI
        }
    }

    assert(max_val as int - min_val as int <= i32::MAX as int);
    assert(max_val as int - min_val as int >= i32::MIN as int);
    assert(max_val >= min_val);

    max_val - min_val
}

}

//             max_val as int - min_val as int <= i32::MAX as int, // Added by AI, for assertion fail
//   None: max_val as int - min_val as int <= i32::MAX as int

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 6
// Safe: True