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

proof fn lemma_monotonic_sum(arr: Seq<i64>, i: int, j: int)
    requires
        0 <= i <= j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i)) <= sum_to(arr.subrange(0, j)),
    decreases j - i
{
    if i < j {
        lemma_monotonic_sum(arr, i, j - 1);
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
            forall|i: int|
                0 <= i < index ==> sum == (sum_to(arr@.subrange(0, i as int)) + arr@[i] as i128),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr@[k] == arr@[k],
            sum <= i128::MAX,
            sum >= i128::MIN,
            sum + arr[( index ) as int] as i128 <= i128::MAX, // Added by AI, for assertion fail
            sum + arr[( index ) as int] as i128 >= i128::MIN, // Added by AI, for assertion fail
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX);
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         assert(sum + arr[( index ) as int] as i128 >= i128::MIN);
//   assertion failed: sum + arr[( index ) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: True