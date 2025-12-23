
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

proof fn lemma_monotonic(arr: Seq<i64>, i: int)
    requires
        0 <= i <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i)) <= sum_to(arr),
    decreases arr.len() - i
{
    if i < arr.len() {
        lemma_monotonic(arr, i + 1);
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
            arr.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr.len(),
    {
        assert!(sum_to(arr@.subrange(0, index as int + 1)) <= sum_to(arr@));
        
        // Assertion to check for potential overflow/underflow
        assert!(sum + arr[index] as i128 <= sum_to(arr@) as i128);
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}
} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False