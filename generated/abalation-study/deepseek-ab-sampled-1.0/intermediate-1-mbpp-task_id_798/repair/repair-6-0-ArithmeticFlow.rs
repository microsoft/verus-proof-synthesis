
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

proof fn lemma_monotonic_sum(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(arr.take(j - 1 as int).drop_last()) <= sum_to(arr.take(j as int)),
{
    // Monotonicity proof via induction on j
    if j == 0 {
        // Base case: j = 0, sum_to is 0
    } else {
        lemma_monotonic_sum(i, j - 1);
        // By induction hypothesis, the sum increases as elements are added
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
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        assert(sum + arr[index] as i128 <= my_upper_bound()) by {
            lemma_monotonic_sum(index as nat, index + 1 as nat);
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

spec fn my_upper_bound() -> i128 {
    // Define the upper bound based on maximum possible sum
    1000000 // Example value, adjust as needed
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True