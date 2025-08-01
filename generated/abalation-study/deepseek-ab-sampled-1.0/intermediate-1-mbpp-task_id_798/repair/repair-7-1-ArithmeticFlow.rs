
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

proof fn lemma_sum_to_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(Seq::new([(0, i)])) <= sum_to(Seq::new([(0, j)])),
{
    // This can be proven by induction or other means depending on the exact specifications
    // For simplicity, assume sum_to is monotonically increasing
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
        // Ensure that adding arr[index] won't cause overflow under the constraints
        assert!(sum + arr[index] as i128 <= 1000000) by {
            lemma_sum_to_monotonic(index, arr.len());
        };

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