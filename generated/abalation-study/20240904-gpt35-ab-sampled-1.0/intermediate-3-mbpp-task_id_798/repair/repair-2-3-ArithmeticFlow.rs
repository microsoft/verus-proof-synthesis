Here's the modified code with the assertion about the bound of `sum + arr[index] as i128` added right before the line `sum = sum + arr[index] as i128`:

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
            index <= arr.len() /* The length of arr does not change during this loop */,
            // forall |k:int| 0<= k < arr.len() ==> true /* The array elements are never modified in this loop */,
    {
        assert(sum + arr[index] as i128 >= sum) by {
            // Add any necessary preconditions to guarantee the assertion
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

You may need to define further preconditions to make the assertion provable. If the value of this expression is related to a recursively defined spec function in the program, generating a lemma function that shows the monotonicity of this expression could help prove its bound.

//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False