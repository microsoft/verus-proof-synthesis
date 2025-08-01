
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, index: nat)
    requires
        index < arr.len(),
    ensures
        sum_to(arr.subrange(0, index as int + 1)) >= sum_to(arr.subrange(0, index as int)),
{
    // This lemma proves that sum_to is monotonic with respect to the subrange
    if index > 0 {
        lemma_sum_to_monotonic(arr, ( index - 1 ) as nat);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            arr.len() == arr@.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // arr is not modified in the loop
    {
        // Add assertion to avoid overflow
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128) by {
            lemma_sum_to_monotonic(arr@, index as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True