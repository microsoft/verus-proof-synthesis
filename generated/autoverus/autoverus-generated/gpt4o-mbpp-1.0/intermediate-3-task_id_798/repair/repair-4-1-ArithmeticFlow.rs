
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

// Lemma to show monotonic increase of sum_to
proof fn lemma_sum_to_monotonic(arr: Seq<i64>, n: nat)
    requires
        n <= arr.len(),
    ensures
        sum_to(arr.subrange(0, ( n ) as int)) <= sum_to(arr),
{
    if n < arr.len() {
        lemma_sum_to_monotonic(arr, n + 1);
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
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
    {
        // Check that the addition won't overflow or underflow
        assert(
            sum.wrapping_add(arr[( index ) as int] as i128) == sum + arr[( index ) as int] as i128
            && sum + arr[( index ) as int] as i128 <= sum_to(arr@)
        ) by {
            lemma_sum_to_monotonic(arr@, ( index ) as nat);
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