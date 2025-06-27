
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k],
    {
        let arr_element = arr[index] as i128;
        
        // Adding the assertion to prevent overflow/underflow
        assert!(
            (sum >= 0 && arr_element >= 0 && sum <= i128::MAX - arr_element) ||
            (sum <= 0 && arr_element <= 0 && sum >= i128::MIN - arr_element) ||
            (sum >= 0 && arr_element <= 0) ||
            (sum <= 0 && arr_element >= 0),
            "Addition of `sum` and `arr_element` would cause overflow or underflow"
        );

        sum = sum + arr_element;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False