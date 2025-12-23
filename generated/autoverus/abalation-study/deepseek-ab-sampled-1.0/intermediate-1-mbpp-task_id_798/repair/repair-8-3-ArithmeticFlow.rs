
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

proof fn lemma_sum_to_monotonic(i: int, j: int, arr: Seq<i64>)
    requires
        i <= j,
        i >= 0,
        j >= 0,
        j <= arr.len() as int,
        i <= arr.len() as int,
    ensures
        sum_to(arr.take(i)) <= sum_to(arr.take(j)),
{
    if i >= 0 {
        if i < arr.len() as int {
            lemma_sum_to_monotonic(i + 1, j, arr);
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
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        assert(sum + arr[( index ) as int] as i128 == sum_to(arr@.take((index + 1) as int))) by {
            lemma_sum_to_monotonic(index as int, index as int + 1, arr@.clone());
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