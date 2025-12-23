
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
        sum_to(Seq::new().take(i as int)) <= sum_to(Seq::new().take(j as int)),
{
    if i < j {
        lemma_sum_to_monotonic(i, (j - 1) as nat);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    requires
        sum_to(arr@) <= i128::MAX,
        sum_to(arr@) >= i128::MIN,
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0_i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            sum_to(arr@.take(index as int)) <= i128::MAX,
            sum_to(arr@.take(index as int)) >= i128::MIN,
    {
        let value = arr[index] as i128;
        assert!(sum + value <= i128::MAX) by {
            lemma_sum_to_monotonic(index as nat, (index + 1) as nat);
        };
        assert!(sum + value >= i128::MIN) by {
            lemma_sum_to_monotonic(index as nat, (index + 1) as nat);
        };

        sum = sum + value;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False