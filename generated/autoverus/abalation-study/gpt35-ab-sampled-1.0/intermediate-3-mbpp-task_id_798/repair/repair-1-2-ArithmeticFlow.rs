
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

proof fn lemma_sum_bound(arr: &Vec<i64>, index: usize, sum: i128)
    requires
        sum_to(arr[..index].to_vec()) + arr[index] as int <= i128::max_value() as int && sum_to(arr[..index].to_vec()) + arr[index] as int >= i128::min_value() as int,
    ensures
        sum + arr[index] as i128 <= i128::max_value() && sum + arr[index] as i128 >= i128::min_value(),
{
    // Proof of the bound
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len() /* The length of arr does not change during this loop */,
            // forall |k:int| 0<= k < arr.len() ==> true /* The array elements are never modified in this loop */,
    {
        lemma_sum_bound(arr, index, sum) by {
            // add a proof statement to bound the sum + arr[index] as i128
        }
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