
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

proof fn lemma_sum_to_bounds(arr: Seq<i64>)
    ensures
        sum_to(arr) <= arr.len() as int * i64::MAX as int,
{
    if arr.len() == 0 {
        assert(sum_to(arr) == 0);
    } else {
        lemma_sum_to_bounds(arr.drop_last());
        assert(sum_to(arr) == sum_to(arr.drop_last()) + arr.last());
        assert(sum_to(arr) <= (arr.len() - 1) as int * i64::MAX as int + arr.last());
        assert(sum_to(arr) <= arr.len() as int * i64::MAX as int);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    lemma_sum_to_bounds(arr@); // Prove the bounds before the loop
    while index < arr.len()
        invariant
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
    {
        let next_sum = sum + arr[index] as i128;
        // Add assertion to check bounds before the critical line
        assert(next_sum <= arr.len() as i128 * i64::MAX as i128);
        sum = next_sum;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False