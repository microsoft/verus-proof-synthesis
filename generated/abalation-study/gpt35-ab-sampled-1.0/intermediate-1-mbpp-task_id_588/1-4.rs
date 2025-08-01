
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_seq_drop_last(v: Seq<i32>, i: int)
    requires 
        0 <= i < v.len(),
    ensures
        v.drop_last().len() == v.len() - 1,
{
    assert(v.drop_last().len() == v.len() - 1);
}

proof fn lemma_seq_first_last_consistency(v: Seq<i32>)
    requires 
        v.len() > 0,
    ensures
        v.first() == v.subrange(0, 1).first() && v.drop_last().last() == v.last(),
{
    assert(v.first() == v.subrange(0, 1).first() && v.drop_last().last() == v.last());
}

proof fn lemma_seq_subrange_max_min(v: Seq<i32>, first: int, last: int, min_val: int, max_val: int)
    requires 
        0 <= first <= last < v.len(),
        min_val <= v[first] && v[last] <= max_val, 
    ensures
        min_val <= min_rcur(v.subrange(first, last + 1)) && max_rcur(v.subrange(first, last + 1)) <= max_val,
{
    assert(min_val <= min_rcur(v.subrange(first, last + 1)) && max_rcur(v.subrange(first, last + 1)) <= max_val);
}

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
            0 < arr.len(), 
            0 <= index <= arr.len(),
            forall |i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i] < i32::MAX / 2,
            forall |i: int| index <= i < arr.len() ==ᐱ> min_val <= arr[i] <= max_val,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
        proof {
            lemma_seq_drop_last(arr@, index - 1);
            lemma_seq_first_last_consistency(arr@);
            lemma_seq_subrange_max_min(arr@, 0, index - 1, min_val, max_val);
        }
    }
    max_val - min_val

}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1