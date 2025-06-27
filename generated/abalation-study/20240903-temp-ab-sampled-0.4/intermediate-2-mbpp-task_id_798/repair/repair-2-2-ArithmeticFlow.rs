
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

proof fn lemma_monotonic_sum_to(arr: Seq<i64>, i: nat, j: nat)
    requires
        i <= j,
        j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, ( i ) as int)) <= sum_to(arr.subrange(0, ( j ) as int)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_sum_to(arr, i, ( j - 1 ) as nat);
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
            arr.len() <= 1000,
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            arr.len() <= 1000,
            arr.len() == arr.len(),
    {
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@)); // Assertion to check bounds
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!






//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: True