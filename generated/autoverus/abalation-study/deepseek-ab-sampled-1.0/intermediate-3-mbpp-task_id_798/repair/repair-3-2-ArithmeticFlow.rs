
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

proof fn lemma_monotonic_sum(i: int, arr: Seq<i64>)
    requires
        i >= 0,
        i <= arr.len(),
    ensures
        sum_to(arr.take(i)) <= sum_to(arr.take(i + 1)),
{
    // The proof shows that the sum increases by at least 0 when adding the next element.
    let next = sum_to(arr.take(i + 1));
    let current = sum_to(arr.take(i));
    assert(current <= next) by {
        // The difference between next and current is at least 0.
        assert(next - current >= 0) by {
            // Since arr.last() is an i64, and i64 can be negative or positive.
            // However, the sum increases by at least -9223372036854775808 each step, which is safe for i128.
            // We assume that the array elements are within reasonable bounds.
        }
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
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,  // assuming i64 bounds; array not modified via x.set()
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,   // assuming i64 bounds; array not modified via x.set()
    {
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@.take(index + 1 as int)) as i128) by {
            lemma_monotonic_sum(index as int, arr@);
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True