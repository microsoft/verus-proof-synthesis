
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
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            index < arr.len(),
            arr.len() == arr.len(),  // Invariant specifying the length of the array
    {
        assert({
            let next = sum + arr[index] as i128;
            next >= i128::MIN && next <= i128::MAX
        }, "Addition would cause overflow or underflow");

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

Explanation:

1. **Assertion**: Before the addition operation `sum = sum + arr[index] as i128;`, we introduce an assertion:
    rust
    assert({
        let next = sum + arr[index] as i128;
        next >= i128::MIN && next <= i128::MAX
    }, "Addition would cause overflow or underflow");
    

//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False