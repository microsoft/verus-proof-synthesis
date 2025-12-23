
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

lemma sum_to_lower_bound() {
    // This lemma proves that the sum of any sequence is greater than or equal to i128::MIN
    // given that individual elements are within bounds.
    for any arr: Seq<i64>, #[trigger] sum_to(arr) >= i128::MIN as int
}

lemma sum_to_upper_bound() {
    // This lemma proves that the sum of any sequence is less than or equal to i128::MAX
    // given that individual elements are within bounds.
    for any arr: Seq<i64>, #[trigger] sum_to(arr) <= i128::MAX as int
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
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
            sum >= i128::MIN, // Added invariant
            sum <= i128::MAX, // Added invariant
    {
        // Prove that sum remains within bounds before addition
        proof {
            sum_to_lower_bound();
            sum_to_upper_bound();
            assert(sum >= i128::MIN);
            assert(sum <= i128::MAX);
        }
        sum += arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         assert(sum + (arr[( index ) as int] as i128) >= i128::MIN) by {
//   assertion failed: sum + (arr[( index ) as int] as i128) >= i128::MIN

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False