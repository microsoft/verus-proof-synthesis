
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
        sum_to(arr.take(index + 1)) <= sum_to(arr),
{
    if index == 0 {
        // Base case: sum_to(arr.take(1)) <= sum_to(arr)
        assert(sum_to(arr.take(1)) == arr[0]);
        assert(sum_to(arr.take(1)) <= sum_to(arr));
    } else {
        // Inductive case
        lemma_sum_to_monotonic(arr, index - 1);
        assert(sum_to(arr.take(index + 1)) == sum_to(arr.take(index)) + arr[index]);
        assert(sum_to(arr.take(index)) <= sum_to(arr));
        assert(sum_to(arr.take(index + 1)) <= sum_to(arr));
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len() 
        invariant index <= arr.len(),
        invariant sum == sum_to(arr@.take(index)),
    {
        assert(sum + arr[index] as i128 <= sum_to(arr@)) by {
            lemma_sum_to_monotonic(arr@, index);
        };
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False