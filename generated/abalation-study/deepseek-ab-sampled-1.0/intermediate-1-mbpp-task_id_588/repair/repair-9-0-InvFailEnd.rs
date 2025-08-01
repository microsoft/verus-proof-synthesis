
use vstd::prelude::*;

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

    proof fn lemma_bounded_difference(seq: Seq<i32>)
        requires
            seq.len() > 0,
            forall|i: int| 0 <= i < seq.len() ==> i32::MIN / 2 < seq[i as int] < i32::MAX / 2,
        ensures
            max_rcur(seq) - min_rcur(seq) <= i32::MAX as int,
            max_rcur(seq) - min_rcur(seq) >= i32::MIN as int,
    {
        let min_val = min_rcur(seq);
        let max_val = max_rcur(seq);
        assert(max_val <= i32::MAX as int);
        assert(min_val >= i32::MIN as int);
        assert(max_val - min_val <= i32::MAX as int);
        assert(max_val - min_val >= i32::MIN as int);
    }

    fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < arr[i] < i32::MAX / 2,
        ensures
            diff == max_rcur(arr@) - min_rcur(arr@),
    {
        let mut min_val = arr[0];
        let mut max_val = arr[0];
        let mut index = 1;
        while index < arr.len()
            invariant
                0 <= index <= arr.len(),
                max_val == max_rcur(Seq::new(index, |i: int| arr[i as int] as i32)),
                min_val == min_rcur(Seq::new(index, |i: int| arr[i as int] as i32)),
                forall|i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i],
                forall|i: int| 0 <= i < index ==> arr[i] < i32::MAX / 2,
                max_val - min_val <= i32::MAX as int,
                max_val - min_val >= i32::MIN as int,
                min_val >= i32::MIN as int,
                max_val <= i32::MAX as int,
        {
            if arr[index] <= min_val {
                min_val = arr[index];
            } else if arr[index] > max_val {
                max_val = arr[index];
            }
            index += 1;

            proof {
                // Establish that min_val and max_val are within the valid 32-bit integer range
                assert(min_val >= i32::MIN as int);
                assert(max_val <= i32::MAX as int);

                // Prove that the difference is within bounds using the lemma
                lemma_bounded_difference(Seq::new(index, |i: int| arr[i as int] as i32));
            }
        }

        // Assertion to prevent underflow/overflow
        assert(i32::MIN <= (max_val - min_val) && (max_val - min_val) <= i32::MAX) by {
            lemma_bounded_difference(arr@);
        };

        max_val - min_val
    }
} // verus!


//             max_val - min_val <= i32::MAX as int,
//   None: max_val - min_val <= i32::MAX as int

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False