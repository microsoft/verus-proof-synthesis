
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

proof fn lemma_sum_to_inc(arr: Seq<i64>, n: nat)
    requires
        n <= arr.len(),
        forall |k: int| 0 <= k < n ==> arr[k] <= 9223372036854775807,
        forall |k: int| 0 <= k < n ==> arr[k] >= -9223372036854775808
{
    if n < arr.len() {
        lemma_sum_to_inc(arr, n + 1 as nat);
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
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_inc(arr@, index as nat);
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
// Safe: True