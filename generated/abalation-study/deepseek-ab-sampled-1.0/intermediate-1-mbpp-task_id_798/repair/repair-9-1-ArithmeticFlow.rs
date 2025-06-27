
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

proof fn lemma_sum_safe(i: nat, j: nat)
    requires
        j <= i,
        sum_to(arr@.take(j as int)) <= 2^127 - 1,
        sum_to(arr@.take(j as int)) >= -2^127,
    ensures
        sum_to(arr@.take(i as int)) <= 2^127 - 1,
        sum_to(arr@.take(i as int)) >= -2^127,
    decreases i
{
    if i == 0 {
        return;
    }
    lemma_sum_safe(j, i - 1);
    assert(sum_to(arr@.take(i as int)) <= 2^127 - 1 && sum_to(arr@.take(i as int)) >= -2^127) by {
        // Prove by induction that sum_to remains within i128 bounds.
        // Use properties of sum_to and lemma_sum_safe to ensure the sum is bounded.
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
        assert(sum + arr[index] as i128 <= 2^127 - 1 && sum + arr[index] as i128 >= -2^127) by {
            // Use the lemma to ensure that adding the next element doesn't cause overflow.
            lemma_sum_safe(index as nat, index as nat);
        };
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True