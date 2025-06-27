
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

proof fn lemma_monotonic_max(i: nat, j: nat, seq: Seq<i32>)
    requires
        i <= j,
        seq.len() >= j,
    ensures
        max_rcur(Seq::new(j, |k: int| seq[k as int])) >= max_rcur(Seq::new(i, |k: int| seq[k as int])),
    decreases j
{
    if i < j {
        lemma_monotonic_max(i, (j-1) as nat, seq.drop_last());
    }
}

proof fn lemma_monotonic_min(i: nat, j: nat, seq: Seq<i32>)
    requires
        i <= j,
        seq.len() >= j,
    ensures
        min_rcur(Seq::new(i, |k: int| seq[k as int])) <= min_rcur(Seq::new(j, |k: int| seq[k as int])),
    decreases j
{
    if i < j {
        lemma_monotonic_min((i+1) as nat, j, seq.drop_last());
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
            0 <= index <= arr.len(),
            max_val == max_rcur(Seq::new((index) as nat, |i: int| arr[i as int] as i32)),
            min_val == min_rcur(Seq::new((index) as nat, |i: int| arr[i as int] as i32)),
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i],
            forall|i: int| 0 <= i < index ==> arr[i] < i32::MAX / 2,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to prevent underflow/overflow
    assert(i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX) by {
        // Using the lemmas to prove the difference is within bounds
        lemma_monotonic_max(0, arr.len() as nat, arr@);
        lemma_monotonic_min(0, arr.len() as nat, arr@);
    };

    max_val - min_val
}

} // verus!


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 8
// Safe: True