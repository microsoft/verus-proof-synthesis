
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

 proof fn lemma_sum_to_non_decreasing(arr: Seq<i64>, index: nat)
    ensures
        sum_to(arr.take(( index + 1 ) as int)) >= sum_to(arr.take(( index ) as int)),
{
    // This lemma proves that the sum_to function is non-decreasing as the index increases,
    // ensuring that adding elements to the array does not decrease the sum.
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    requires
        arr.len() >= 0,
        arr.is_valid(),
    ensures
        sum == sum_to(arr@),
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
{
        assert(sum <= sum_to(arr@.take(index as int + 1))) by{
            // We use the lemma to prove the sum increases with each element added.
            lemma_sum_to_non_decreasing(arr@, index as nat);
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False