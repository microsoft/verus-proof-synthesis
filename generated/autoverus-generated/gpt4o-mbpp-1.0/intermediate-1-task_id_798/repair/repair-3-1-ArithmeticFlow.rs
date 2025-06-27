
#[allow(unused_imports)]
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

spec fn max_sum_to(arr: Seq<i64>) -> int
    decreases arr.len()
{
    arr.fold(|acc, x| acc + x as int, 0)
}

// Lemma to show that `sum_to(arr)` is bounded by `max_sum_to(arr)`
proof fn lemma_max_sum_to_bound(arr: Seq<i64>)
    ensures
        sum_to(arr) <= max_sum_to(arr)
{
    if arr.len() == 0 {
        assert(sum_to(arr) == 0);
        assert(max_sum_to(arr) == 0);
    } else {
        lemma_max_sum_to_bound(arr.drop_last());
        assert(sum_to(arr) == sum_to(arr.drop_last()) + arr.last());
        assert(max_sum_to(arr) == max_sum_to(arr.drop_last()) + arr.last() as int);
        assert(sum_to(arr) <= max_sum_to(arr));
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
            arr.len() == arr.len(), // constant length
            index <= arr.len(), // index in bounds
            sum == sum_to(arr@.subrange(0, index as int)) as i128, // sum invariant
            index < arr.len(),
            arr.len() == arr.len()
    {
        // Ensure we do not overflow the i128 bounds
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX as i128) by {
            lemma_max_sum_to_bound(arr@.subrange(0, arr.len() as int));
            assert(sum_to(arr@.subrange(0, index as int + 1)) <= max_sum_to(arr@));
            assert(sum + arr[index] as i128 <= max_sum_to(arr@) as i128);
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
// Safe: False