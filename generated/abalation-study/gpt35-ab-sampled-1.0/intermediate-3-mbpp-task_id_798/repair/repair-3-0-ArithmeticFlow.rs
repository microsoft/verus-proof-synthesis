
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

proof fn sum_to_monotonic(arr: Seq<i64>, i: int, j: int)
    requires
        i <= j,
    ensures
        sum_to(arr.slice(0, (i as nat))) <= sum_to(arr.slice(0, (j as nat))),
    decreases (j - i)
{
    if i < j {
        sum_to_monotonic(arr, i, (j - 1) as int);
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
            sum + arr[( index ) as int] as i128 >= sum /* Assertion to prevent overflow */,
    {
        assert(sum_to(arr.slice(0, (index as nat))) <= sum) by {
            sum_to_monotonic(arr.slice(0, (index as nat)), 0, index as int);
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}
} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True