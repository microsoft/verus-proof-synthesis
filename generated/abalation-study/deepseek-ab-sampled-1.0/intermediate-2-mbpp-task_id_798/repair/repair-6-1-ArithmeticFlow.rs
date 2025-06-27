
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

// Lemma to establish that sum_to is non-decreasing with respect to array length
proof fn lemma_sum_to_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(arr.take(i as int)) <= sum_to(arr.take(j as int)),
    decreases j
{
    if i < j {
        lemma_sum_to_monotonic(i, (j - 1) as nat);
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
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take((index) as int)),
    {
        // Ensure that adding the next element doesn't cause overflow/underflow
        assert(sum + arr[index] as i128 <= i128::MAX && sum + arr[index] as i128 >= i128::MIN) by {
            // Use the lemma to show sum_to grows appropriately
            lemma_sum_to_monotonic(index as nat, (index + 1) as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True