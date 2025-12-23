
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

    assert(0 <= index < arr.len()) by { } // Added by AI
    while index < arr.len()
        invariant
            0 <= index < arr.len(), // The array arr is never modified in the loop
            sum + arr[(index) as int] as i128 >= i128::MIN, // Added by AI, for assertion fail
            sum + arr[(index) as int] as i128 <= i128::MAX, // Added by AI, for assertion fail
    {
        sum = sum + arr[index] as i128;
        index += 1;

        proof{
            assert(sum + arr[(index) as int] as i128 >= i128::MIN); // Added by AI
            assert(sum + arr[(index) as int] as i128 <= i128::MAX); // Added by AI
            assert(index < arr.len()); // Modified by AI, for assertion fix
        }
    }
    sum
}
} // verus!


//             assert(sum + arr[(index) as int] as i128 <= i128::MAX); // Added by AI
//   assertion failed: sum + arr[(index) as int] as i128 <= i128::MAX

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True