
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

proof fn lemma_sum_to_monotonic(i: usize, j: usize) 
    requires 
        i <= j,
    ensures 
        sum_to(arr@.take(i as int)) <= sum_to(arr@.take(j as int)),
    decreases j
{
    if j > i {
        lemma_sum_to_monotonic(i, j - 1);
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
            sum == sum_to(arr@.take((index) as int)),
            0 <= index <= arr.len() ==> sum >= 0 && sum <= (i128::MAX as i128)
    {
        sum = sum + arr[index] as i128;

        if index + 1 != arr.len() {
            assert (sum + arr[index + 1] as i128 <= (i128::MAX as i128)) by {
                lemma_sum_to_monotonic((index + 1) as usize, arr.len() as usize);
            };
        }

        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True