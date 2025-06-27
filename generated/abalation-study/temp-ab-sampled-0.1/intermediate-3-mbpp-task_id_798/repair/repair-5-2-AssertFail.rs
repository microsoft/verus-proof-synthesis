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

proof fn lemma_monotonic(arr: Seq<i64>, index: nat)
    requires
        index <= arr.len(),
    ensures
        sum_to(arr.take(( index ) as int)) <= sum_to(arr),
    decreases arr.len() - index
{
    if index < arr.len() {
        lemma_monotonic(arr, index + 1);
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
            sum_to(arr@.take(index as int)) == sum, // Added by AI, for assertion fail
    {
        // Assertion to ensure no overflow/underflow
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
            lemma_monotonic(arr@, index as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

//         assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
//   assertion failed: sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: True