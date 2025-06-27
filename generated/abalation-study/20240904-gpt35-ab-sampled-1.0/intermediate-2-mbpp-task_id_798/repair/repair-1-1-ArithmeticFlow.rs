
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
            0 <= index < arr.len(), // The array arr is never modified in the loop
    {
        assert(sum + arr[( index ) as int] as i128 >= sum) by {
            // Use a lemma function to demonstrate the monotonicity of the addition
            lemma_monotonic_sum(sum, arr[( index ) as int] as i128);
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}


proof fn lemma_monotonic_sum(a: i128, b: i128)
    ensures
        a <= a + b,
{
    // Prove that the addition is monotonic
    // (implementation of the lemma function)
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: True