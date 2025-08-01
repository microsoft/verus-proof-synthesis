
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    spec fn sum_to(arr: Seq<i64>) -> u64
        decreases arr.len(),
    {
        if arr.len() == 0 {
            0
        } else {
            ( sum_to(arr.drop_last()) + arr.last() ) as u64
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
                sum == sum_to(arr@.take((index) as int)),
        {
            let current = arr[index] as i128;
            if current > 0i128 && sum > i128::MAX - current {
                sum = i128::MAX;
            } else if current < 0i128 && sum < i128::MIN - current {
                sum = i128::MIN;
            } else {
                sum += current;
            }
            index += 1;
        }
        sum
    }
}



//         assert(sum + (arr[( index ) as int] as i128) as i128 >= i128::MIN);
//   assertion failed: sum + (arr[( index ) as int] as i128) as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False