
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, i: nat)
    requires
        i < arr.len(),
    ensures
        sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, (i + 1) as int)),
{
    if i == 0 {
        assert(sum_to(arr.subrange(0, 0)) == 0);
        assert(sum_to(arr.subrange(0, 1)) == arr.index(0));
    } else {
        lemma_sum_to_monotonic(arr, ( i - 1 ) as nat);
        assert(sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, (i + 1) as int)));
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
            arr.len() <= 1000,
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            arr.len() <= 1000,
            arr.len() == arr.len(),
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
            lemma_sum_to_monotonic(arr@, index as nat);
        };
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True