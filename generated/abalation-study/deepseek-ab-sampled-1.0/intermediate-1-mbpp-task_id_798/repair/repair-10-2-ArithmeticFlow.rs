
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
        sum_to(arr@.take(i)) <= sum_to(arr@.take(j)),
    decreases j
{
    if i < j {
        lemma_sum_to_monotonic(i, (j as nat) - 1);
        lemma_sum_to_monotonic((i as nat) + 1, j);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
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
            arr.len() >= 0,
    {
        // Assertion to prevent overflow/underflow
        assert(
            sum + arr[index] as i128 <= Int::max() as i128
        ) by {
            lemma_sum_to_monotonic(index as nat, (index + 1) as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False