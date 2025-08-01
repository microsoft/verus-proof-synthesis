
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
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    proof {
        lemma_min_value_holds(arr@, min_val);
        lemma_max_value_holds(arr@, max_val);

        let seq_arr = arr@;
        let max_prf = max_rcur(seq_arr) as i32;
        let min_prf = min_rcur(seq_arr) as i32;
        assert(max_prf == max_val); 
        assert(min_prf == min_val); 
    }
    max_val - min_val
}

proof fn lemma_min_value_holds(arr: Seq<i32>, min_val: i32) 
    ensures
        min_rcur(arr) == min_val as int,
{
    assert_forall_by(|i: int| {
        requires(0 <= i && i < arr.len());
        ensures(arr[i] >= min_val);
    }, |i| {
        if i == _ { // Placeholder for proof, actual condition needs implementation based on the loop and variable updates
            // The proof strategy here is to use induction or specific properties verified in the loop invariants to show that min_val must be <= all elements in arr
        }
    });
}

proof fn lemma_max_value_holds(arr: Seq<i32>, max_val: i32)
    ensures
        max_rcur(arr) == max_val as int,
{
    assert_forall_by(|i: int| {
        requires(0 <= i && i < arr.len());
        ensures(arr[i] <= max_val);
    }, |i| {
        if i == _ { // Placeholder for proof, actual condition needs implementation based on the loop and variable updates
            // The proof strategy here is to use induction or specific properties verified in the loop invariants to show that max_val must be >= all elements in arr
        }
    });
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