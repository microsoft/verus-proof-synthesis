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

proof fn lemma_monotonic(arr: Seq<i64>, index: nat)
    requires
        index <= arr.len(),
    ensures
        sum_to(arr.take(( index ) as int)) <= sum_to(arr),
    decreases arr.len() - index
{
    if index < arr.len() {
        lemma_monotonic(arr, index + 1);
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
            sum == sum_to(arr@.take(( index ) as int)),
            sum <= i128::MAX, // Fixed by AI
            sum >= i128::MIN, // Fixed by AI
            index < arr.len() ==> sum + arr[( index ) as int] as i128 <= i128::MAX, // Added by AI, for assertion fail
            index < arr.len() ==> sum + arr[( index ) as int] as i128 >= i128::MIN, // Added by AI, for assertion fail
    {
        assert(index < arr.len() ==> sum + arr[( index ) as int] as i128 <= i128::MAX);
        assert(index < arr.len() ==> sum + arr[( index ) as int] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;

        proof {
            assert(index <= arr.len());
            assert(sum == sum_to(arr@.take(( index ) as int)));
            assert(sum <= i128::MAX);
            assert(sum >= i128::MIN);
            assert(index < arr.len() ==> sum + arr[( index ) as int] as i128 <= i128::MAX);
            assert(index < arr.len() ==> sum + arr[( index ) as int] as i128 >= i128::MIN);
        } // Added by AI
    }
    sum
}

} // verus!
// Score: (1, 4)
// Safe: True