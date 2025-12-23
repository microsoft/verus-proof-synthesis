
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
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
    {
        // Assertion to ensure sum + arr[index] will not overflow
        assert(sum + arr[index] as i128 <= i128::MAX);
        assert(sum + arr[index] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

This added assertion will check that the resulting sum after adding `arr[index]` is within the valid range for an `i128` to prevent any overflow or underflow errors.

Additionally, you might define a lemma to prove a more detailed property about the bounds of `sum_to` if you need stronger guarantees about its behavior. Here is an example of such a lemma that proves the bounds of `sum_to`:

rust
proof fn lemma_sum_to_bound(arr: Seq<i64>)
    ensures
        sum_to(arr) <= arr.len() as int * i64::MAX as int,
        sum_to(arr) >= arr.len() as int * i64::MIN as int,
{
    if arr.len() > 0 {
        let rest = arr.drop_last();
        let last = arr.last();
        lemma_sum_to_bound(rest);
        assert(sum_to(rest) + last <= rest.len() as int * i64::MAX as int + last);
        assert(sum_to(rest) + last >= rest.len() as int * i64::MIN as int + last);
    }
}

You can call this lemma within the loop to help Verus prove the bounds automatically as follows:

rust
while index < arr.len()
    invariant
        arr@.len() == arr.len(),
        index <= arr.len(),
        sum == sum_to(arr@.subrange(0, (index) as int)),
        forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
{
    lemma_sum_to_bound(arr@.subrange(0, (index + 1) as int));
    
    // Assertion to ensure sum + arr[index] will not overflow
    assert(sum + arr[index] as i128 <= i128::MAX);
    assert(sum + arr[index] as i128 >= i128::MIN);

    sum = sum + arr[index] as i128;
    index += 1;
}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: False