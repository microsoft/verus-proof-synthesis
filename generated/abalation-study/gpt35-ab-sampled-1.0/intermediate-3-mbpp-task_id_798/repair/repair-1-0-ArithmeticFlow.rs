
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

lemma fn positive_sum_bound(arr: &Seq<i64>, sum: i128, index: usize)
    requires
        sum_to(arr.slice(0..index)) + arr[index] as Int < i32::MAX,
    ensures
        sum_to(arr.slice(0..index)) + arr[index] as Int + sum < i32::MAX,
{
    // Here we use the fact that sum_to(arr.slice(0..index)) + arr[index] as Int < i32::MAX
    // We can safely add sum to both sides without causing overflow
    // Hence, sum_to(arr.slice(0..index)) + arr[index] as Int + sum < i32::MAX
}

fn sum(arr: &Seq<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |k:usize| 0 <= k < index ==> sum_to(arr.slice(0..k)) + arr[k] as Int < i32::MAX,
    {
        positive_sum_bound(arr, sum, index);
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False