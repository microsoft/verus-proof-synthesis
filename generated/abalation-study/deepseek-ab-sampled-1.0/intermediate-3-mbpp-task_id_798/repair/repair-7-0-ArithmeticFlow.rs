
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

proof fn lemma_sum_to_monotonic(i: int, j: int)
    requires
        i <= j,
        i >= 0,
        j >= 0,
    ensures
        sum_to(Seq::from_func(|_: int| 0, i as usize)) <=
        sum_to(Seq::from_func(|_: int| 0, j as usize)),
{
    if i < j {
        lemma_sum_to_monotonic(i, j-1);
        lemma_sum_to_monotonic(j-1, j);
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
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,  // assuming i64 bounds; array not modified via x.set()
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,   // assuming i64 bounds; array not modified via x.set()
    {
        // Ensure that sum + arr[index] does not cause underflow or overflow
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX)
            by {
                for k in 0..index {
                    lemma_sum_to_monotonic(k, k+1);
                }
        }
        assert(sum + arr[index] as i128 >= i128::MIN)
            by {
                for k in 0..index {
                    lemma_sum_to_monotonic(k, k+1);
                }
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: True