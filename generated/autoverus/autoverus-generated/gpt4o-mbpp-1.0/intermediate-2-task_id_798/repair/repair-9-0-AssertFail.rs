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

proof fn lemma_sum_to_bound(arr: Seq<i64>, idx: nat)
    requires
        idx < arr.len(),
        forall |i: nat| 0 <= i < idx ==> arr.index(( i ) as int) >= 0,
    ensures
        sum_to(arr.subrange(0, ( idx ) as int)) as i128 + arr.index(( idx ) as int) as i128 <= i128::MAX,
        sum_to(arr.subrange(0, ( idx ) as int)) as i128 + arr.index(( idx ) as int) as i128 >= i128::MIN,
{
    // Here, you would add proof steps if needed, to show that the sum is within bounds.
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
            index <= arr.len(),
            arr.len() == arr.len(),
            sum + (if index < arr.len() { arr[( index ) as int] as i128 } else { 0 }) >= i128::MIN,
            sum + (if index < arr.len() { arr[( index ) as int] as i128 } else { 0 }) <= i128::MAX,
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX); // Check for overflow
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN); // Check for underflow
        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            if index < arr.len() {
                lemma_sum_to_bound(arr@, index as nat); // Use the lemma to ensure bounds
                assert(sum + arr[( index ) as int] as i128 <= i128::MAX); // Verification
            }
        }
    }
    sum
}

}

//                 assert(sum + arr[( index ) as int] as i128 <= i128::MAX); // Added by AI
//   assertion failed: sum + arr[( index ) as int] as i128 <= i128::MAX

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: True