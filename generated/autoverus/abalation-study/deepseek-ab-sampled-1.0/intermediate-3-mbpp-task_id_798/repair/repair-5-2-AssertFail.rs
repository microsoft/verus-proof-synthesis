
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(true)]

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
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808i64,
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807i64,
            sum >= (i128::MIN - 9223372036854775807i64 as i128),
            sum <= (i128::MAX + 9223372036854775807i64 as i128),
    {
        let current = arr[index] as i128;
        assert(index < arr.len());
        sum = sum + current;
        index += 1;
    }
    sum
}

} // verus!


//         assert(sum + arr[( index ) as int] as i128 >= i128::MIN);
//   assertion failed: sum + arr[( index ) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False