
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

proof fn lemma_monotonic(arr: Seq<i64>, arr_len: nat, index: nat)
    requires
        index < arr_len,
    ensures
        sum_to(arr.subrange(0, ( index + 1 ) as int)) == sum_to(arr.subrange(0, ( index ) as int)) + arr[( index ) as int],
{
    // This lemma function ensures that the sum_to function is well-formed and monotonic
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
    {
        let next_elem = arr[index] as i128;

        // Assert that sum + next_elem is within the bounds of i128 to prevent overflow/underflow
        assert(sum + next_elem >= i128::MIN && sum + next_elem <= i128::MAX) by {
            // Applying the lemma for monotonicity to ensure logical flow
            lemma_monotonic(arr@, arr.len() as nat, index as nat);
        };

        sum = sum + next_elem;
        index += 1;
    }
    sum
}

}





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: False