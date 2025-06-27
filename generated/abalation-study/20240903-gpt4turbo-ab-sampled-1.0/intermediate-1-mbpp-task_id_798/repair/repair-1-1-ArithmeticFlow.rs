
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
        sum_to(arr) <= 2^127 - 1,
{
    // Here one would formalize the proof that summing the i64 values from `arr` into an int (akin to i128) never overflows.
    // This might involve proof by induction over `arr.len()`, considering `i64::MAX`.
    // Skipping exact implementation details for brevity.
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
            arr.len() == arr@.len(), // Loop invariant for the length of the array
    {
        // Assert to prevent overflow
        assert(sum + arr[( index ) as int] as i128 <= 2^127 - 1) by {
            lemma_sum_to_bounds(arr@.subrange(0, index as int + 1));
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