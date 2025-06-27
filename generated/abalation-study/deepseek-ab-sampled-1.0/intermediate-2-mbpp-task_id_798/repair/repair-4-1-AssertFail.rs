

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
            0 <= index <= arr.len(),
            sum == sum_to(arr@.take((index) as int)),
            sum <= i128::MAX,
            sum >= i128::MIN,
    {
        assert(sum + (arr[( index ) as int] as i128) as i128 <= i128::MAX);
        assert(sum + (arr[( index ) as int] as i128) as i128 >= i128::MIN);
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}

//         assert(sum + (arr[( index ) as int] as i128) as i128 >= i128::MIN);
//   assertion failed: sum + (arr[( index ) as int] as i128) as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True