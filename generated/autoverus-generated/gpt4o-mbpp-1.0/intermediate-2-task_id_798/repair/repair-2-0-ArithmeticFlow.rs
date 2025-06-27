
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

proof fn lemma_sum_to_monotone(arr: Seq<i64>, n: int)
    requires
        0 <= n <= arr.len(),
    ensures
        sum_to(arr.subrange(0, n)) <= sum_to(arr)
{
    if n < arr.len() {
        lemma_sum_to_monotone(arr, n + 1);
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
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            arr.len() == arr.len(),  // Invariant specifying the length of the array
    {
        // Assertion to make sure the addition doesn't overflow/underflow
        assert((sum as i128) + (arr[( index ) as int] as i128) <= i128::MAX) by {
            lemma_sum_to_monotone(arr@, index as int);
        };
        assert((sum as i128) + (arr[( index ) as int] as i128) >= i128::MIN) by {
            lemma_sum_to_monotone(arr@, index as int);
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
// Safe: True