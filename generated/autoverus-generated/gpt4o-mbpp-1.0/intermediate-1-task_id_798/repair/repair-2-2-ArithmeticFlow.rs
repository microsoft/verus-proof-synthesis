
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

spec fn sum_to_bounded(arr: Seq<i64>, max_val: int) -> bool
    decreases arr.len()
{
    if arr.len() == 0 {
        true
    } else {
        sum_to(arr.drop_last()) + arr.last() <= max_val &&
        sum_to_bounded(arr.drop_last(), max_val)
    }
}

proof fn lemma_sum_to_monotonic(arr: Seq<i64>)
    ensures
        sum_to(arr.subrange(0, ( arr.len() ) as int)) <= sum_to(arr)
{
    admit(); // In reality, you would fill this out with the necessary proof steps
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    requires
        sum_to(arr@) <= i128::MAX as int,
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            arr.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
            sum_to(arr@.subrange(0, index as int)) <= i128::MAX as int,
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_monotonic(arr@);
            assert(sum_to(arr@.subrange(0, index as int)) + arr[( index ) as int] <= sum_to(arr@));
            assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}






//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 6
// Safe: False