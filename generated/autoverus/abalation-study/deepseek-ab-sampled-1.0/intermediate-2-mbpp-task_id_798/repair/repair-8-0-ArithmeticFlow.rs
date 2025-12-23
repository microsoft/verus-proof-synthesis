
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

proof fn lemma_sum_to_monotonic(i: int, arr: Seq<i64>)
    requires
        i >= 0,
        arr.len() > i,
        arr[i] >= 0,
    ensures
        sum_to(arr.take(i)) + arr[i] <= sum_to(arr.take(i + 1)),
{
    // Proof that sum_to is non-decreasing as we add elements
    assert (sum_to(arr.take(i + 1)) == sum_to(arr.take(i)) + arr[i]);
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take((index) as int)),
    {
        // Before adding, ensure that adding the next element won't cause overflow
        if index < arr.len() {
            let current = arr[index] as i128;
            let next = sum + current;
            assert(next <= i128::MAX) by { lemma_sum_to_monotonic(( index ) as int, arr@); };
            sum = next;
        }
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: False