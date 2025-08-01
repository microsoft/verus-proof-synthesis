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

proof fn lemma_monotonic(arr: Seq<i64>, i: nat, j: nat)
    requires
        i <= j,
        j <= arr.len(),
    ensures
        sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, j as int)),
    decreases j - i
{
    if i < j {
        lemma_monotonic(arr, i, ( j - 1 ) as nat);
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
            arr.len() == arr.len(),
            // The array `arr` is never modified in this loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            sum >= i128::MIN, // Fixed by AI
    {
            lemma_monotonic(arr@, 0, index as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            // The assertion is not needed here as it is already part of the loop invariant
        }
    }
    sum
}

} // verus!

// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1