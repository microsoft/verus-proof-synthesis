
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
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr@.len(),
    {
        // New Assertion
        assert(0 <= sum + arr[( index ) as int] as i128) by {
            // Here, you would ideally use a lemma that argues about the monotonically increasing nature of sum
            // and ensures that each addition is within the bounds of i128 considering the maximum possible sum_to value.
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True