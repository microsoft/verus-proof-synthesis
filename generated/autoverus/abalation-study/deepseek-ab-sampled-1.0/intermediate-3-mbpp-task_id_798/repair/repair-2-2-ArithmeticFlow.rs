
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

proof fn lemma_sum_to_monotonic(left: Seq<i64>, right: Seq<i64>)
    requires
        left.len() < right.len() &&
        left == right.take(( left.len() ) as int),
    ensures
        sum_to(left) <= sum_to(right),
    decreases sum_to(right) - sum_to(left)
{
    if sum_to(left) > sum_to(right) {
        lemma_sum_to_monotonic(left.take(left.len() - 1), right.take(( left.len() ) as int));
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
            0 <= index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0 <= k < index ==> (-9223372036854775808 <= arr[k] &&
                                               arr[k] <= 9223372036854775807),
            sum <= sum_to(arr@.take(index as int)) + sum_to(arr@.drop_front(index as int)),
    {
        assert(sum + arr[index] as i128 as int <= sum_to(arr@)) by {
            lemma_sum_to_monotonic(arr@.take(index as int), arr@.take((index + 1) as int));
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True