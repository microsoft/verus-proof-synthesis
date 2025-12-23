
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, index: nat)
    requires
        index < arr.len(),
    ensures
        sum_to(arr.subrange(0, index as int)) <= sum_to(arr)
{
    // The lemma should prove that the sum of a subrange cannot exceed the sum of the entire range
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
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@)) by {
            lemma_sum_to_monotonic(arr@, index as nat);
            assert(sum_to(arr@.subrange(0, index as int)) + (arr[( index ) as int] as int) == sum_to(arr@.subrange(0, index as int + 1)));
        };
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: True