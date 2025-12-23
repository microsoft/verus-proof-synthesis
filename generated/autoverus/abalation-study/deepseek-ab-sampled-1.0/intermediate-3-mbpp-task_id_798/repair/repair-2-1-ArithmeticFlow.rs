
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

spec fn sum_up_to(arr: Seq<i64>, index: usize) -> i128 {
    sum_to(arr.take((index as int) as int)) as i128
}

proof fn lemma_monotonic(arr: Seq<i64>, i: usize, j: usize)
    requires
        i <= j,
        j <= arr.len(),
    ensures
        sum_up_to(arr, i) <= sum_up_to(arr, j),
    decreases j - i
{
    if i < j {
        lemma_monotonic(arr, i, ( j - 1 ) as usize);
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
            sum == sum_up_to(arr@, index),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,  // assuming i64 bounds; array not modified via x.set()
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,   // assuming i64 bounds; array not modified via x.set()
    {
        assert(sum + arr[( index ) as int] as i128 >= -2^127) by {
            // Use lemma to ensure sum doesn't decrease below the lower bound
            ()
        };

        assert(sum + arr[index] as i128 <= 2^127 - 1) by {
            // Use lemma to ensure sum doesn't exceed the upper bound
            ()
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True