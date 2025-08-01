
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

proof fn lemma_sum_monotonic(i: nat, j: nat, arr: Seq<i64>)
    requires
        i <= j,
        i <= arr.len(),
        j <= arr.len(),
    ensures
        sum_to(arr.take(i as int)) <= sum_to(arr.take(j as int)),
{
    if i < j {
        lemma_sum_monotonic(i, (j - 1) as nat, arr);
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
            sum <= sum_to(arr@),
            index >= 0,
            arr.len() >= 0,
    {
        if index < arr.len() {
            let current_element = arr[index] as i128;
            let next_sum = sum + current_element;

            #[verifier(inline)]
            proof {
                assert(sum + current_element <= sum_to(arr@) as i128) by {
                    lemma_sum_monotonic((index as nat), (arr.len() as nat), arr@);
                }
            }

            sum = next_sum;
        }
        index += 1;
    }
    sum
}
}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False