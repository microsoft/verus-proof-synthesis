
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

proof fn lemma_monotonic_sum_to(arr1: Seq<i64>, arr2: Seq<i64>)
    requires
        arr1.len() <= arr2.len(),
    ensures
        sum_to(arr1) <= sum_to(arr2),
    decreases arr2.len()
{
    if arr1.len() < arr2.len() {
        lemma_monotonic_sum_to(arr1, arr2.drop_last());
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
            index <= arr.len() /* The length of arr does not change during this loop */,
            // forall |k:int| 0<= k < arr.len() ==> true /* The array elements are never modified in this loop */,
            assert (sum + arr[index] as i128) >= sum /* Prevent arithmetic underflow */,
            assert (sum + arr[index] as i128) <= std::i128::MAX /* Prevent arithmetic overflow */,
    {
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