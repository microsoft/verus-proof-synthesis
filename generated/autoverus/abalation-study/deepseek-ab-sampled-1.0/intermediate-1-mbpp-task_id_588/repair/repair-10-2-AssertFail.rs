

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
        lemma_monotonic_max(i, ( j as nat - 1 ) as nat, seq.drop_last());
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
        lemma_monotonic_min(i as nat + 1, j, seq.drop_last());
    }
}

proof fn lemma_bounded_difference(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < #[trigger] seq[i as int] < i32::MAX / 2,
    ensures
        max_rcur(seq) <= i32::MAX as int,
        min_rcur(seq) >= i32::MIN as int,
{
    let min_val = min_rcur(seq);
    let max_val = max_rcur(seq);
    assert(max_val <= i32::MAX as int);
    assert(min_val >= i32::MIN as int);
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
            max_val == max_rcur(Seq::new(index as nat, |i: int| arr[i as int] as i32)),
            min_val == min_rcur(Seq::new(index as nat, |i: int| arr[i as int] as i32)),
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i],
            forall|i: int| 0 <= i < index ==> arr[i] < i32::MAX / 2,
            min_val >= i32::MIN as int,
            max_val <= i32::MAX as int,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        
        proof {
            assert(max_val <= i32::MAX as int);
            assert(min_val >= i32::MIN as int);
            lemma_bounded_difference(Seq::new(index as nat, |i: int| arr[i as int] as i32));
        }
    }

    // Assertion to prevent underflow/overflow
    {
        let max_val.safe = max_val;
        let min_val.safe = min_val;
        assert(max_val.safe <= i32::MAX as int);
        assert(min_val.safe >= i32::MIN as int);
        let lower = i32::MIN as int;
        let upper = i32::MAX as int;
        assert(max_val.safe - min_val.safe <= upper - lower);
        let difference = max_val - min_val;
        assert(difference >= i32::MIN, "Difference underflows i32");
        assert(difference <= i32::MAX, "Difference overflows i32");
    }

    max_val.cast() - min_val.cast()
}

} // verus!

//     assert(i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX) by {
//   assertion failed: i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False