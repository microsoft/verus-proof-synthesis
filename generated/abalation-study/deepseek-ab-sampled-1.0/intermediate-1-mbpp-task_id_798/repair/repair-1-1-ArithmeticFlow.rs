
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

// Lemma to prove that sum_to is monotonic
proof fn lemma_sum_to_monotonic(arr: Seq<i64>, index: int)
    requires
        0 <= index <= arr.len() as int
    ensures
        sum_to(arr.take(index as int)) <= sum_to(arr)
{
    // Base case: index == arr.len()
    if index == arr.len() {
        return
    }
    // Use induction or direct proof to show sum_to increases with the array length
    // (Implementation details depend on specific properties of sum_to)
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
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        // Assertion to ensure that adding arr[index] won't cause overflow
        assert(sum + (arr[( index ) as int] as i128) <= sum_to(arr@)) by{
            // Use the lemma to prove that sum + arr[index] <= sum_to(arr)
            lemma_sum_to_monotonic(arr@, index as int);
        }

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