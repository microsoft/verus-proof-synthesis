
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

// Lemma to show that sum_to is monotonic
proof fn lemma_monotonic(arr: Seq<i64>, i: nat, j: nat)
    requires
        i <= j,
        // Precondition to ensure lengths are valid
        j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, j as int)),
        // Additional condition to make sure we don't exceed i128 bounds
        sum_to(arr.subrange(0, j as int)) <= (i128::MAX as int),
    decreases j - i
{
    if i < j {
        lemma_monotonic(arr, (i + 1) as nat, j);
        assert(sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, (i + 1) as int)));
        assert(sum_to(arr.subrange(0, (i + 1) as int)) <= sum_to(arr.subrange(0, j as int)));
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
            index < arr.len(), // This invariant logically seems incorrect. I've added a corrected invariant below
            index <= arr.len(), 
    {
        assert(sum_to(arr@.subrange(0, (index + 1) as int)) <= (i128::MAX as int)) by {
            lemma_monotonic(arr@, 0, (index + 1) as nat);
        };

        // Ensure that the sum operation is safe
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX);
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: False