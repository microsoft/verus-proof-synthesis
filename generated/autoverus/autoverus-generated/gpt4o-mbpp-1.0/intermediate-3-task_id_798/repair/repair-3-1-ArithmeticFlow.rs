
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

proof fn lemma_monotonic(arr: Seq<i64>, k: nat)
    requires
        0 <= k < arr.len(),
    ensures
        sum_to(arr.subrange(0, k as int)) <= sum_to(arr.subrange(0, (k+1) as int)) <= sum_to(arr) 
{
    if k + 1 == arr.len() {
        // Base case, trivially true
        assert(sum_to(arr.subrange(0, k as int)) <= sum_to(arr.subrange(0, (k+1) as int)));
    } else {
        lemma_monotonic(arr, k + 1);
        assert(sum_to(arr.subrange(0, k as int)) <= sum_to(arr.subrange(0, (k+1) as int)));
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
    {
        lemma_monotonic(arr@, index as nat);
        let value_to_add = arr[index] as i128;
        
        // Ensure no overflow/underflow occurs
        assert(sum + value_to_add <= i128::MAX);
        assert(sum + value_to_add >= i128::MIN);

        sum = sum + value_to_add;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False