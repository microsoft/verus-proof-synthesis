
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

proof fn lemma_sum_to_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(Seq[i..j]: Seq<i64>) >= 0,
    decreases j - i
{
    if i < j {
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
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        // Add assertion before the sum update
        assert(sum + (arr[index] as i128) as int <= i128::MAX as int && sum >= (i128::MIN as int)) by {
            lemma_sum_to_monotonic(index as nat, arr.len() as nat);
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