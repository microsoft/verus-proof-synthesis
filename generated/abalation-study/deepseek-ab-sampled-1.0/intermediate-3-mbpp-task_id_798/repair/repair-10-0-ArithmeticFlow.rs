
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

proof fn lemma_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(arr.drop_last(i as int)) <= sum_to(arr.drop_last(j as int)),
    decreases j
{
    if i < j {
        lemma_monotonic(i, (j-1) as nat);
        assert(sum_to(arr.drop_last(j as int)) >= sum_to(arr.drop_last((j-1) as int)));
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
    requires
        arr.len() as i128 * 9223372036854775807i128 <= i128::MAX,
        arr.len() as i128 * (-9223372036854775808i128) >= -i128::MAX,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            sum >= -i128::MAX,
            sum <= i128::MAX,
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,
    {
        assert(sum + (arr[index] as i128) <= i128::MAX) by {
            lemma_monotonic(index as nat, arr.len() as nat);
        };
        assert(sum + (arr[index] as i128) >= -i128::MAX) by {
            lemma_monotonic(index as nat, arr.len() as nat);
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