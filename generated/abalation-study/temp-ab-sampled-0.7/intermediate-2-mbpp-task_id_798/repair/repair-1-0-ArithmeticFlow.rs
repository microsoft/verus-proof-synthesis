
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
        let next_value = arr[index] as i128;
        assert(sum + next_value >= i128::MIN && sum + next_value <= i128::MAX, "Potential overflow/underflow detected.");

        sum = sum + next_value;
        index += 1;
    }
    sum
}

} // verus!

In this modified code, just before the line `sum = sum + arr[index] as i128;`, we compute `next_value` as `arr[index] as i128` and add an assertion:
rust
assert(sum + next_value >= i128::MIN && sum + next_value <= i128::MAX, "Potential overflow/underflow detected.");


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False