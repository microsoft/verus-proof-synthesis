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

proof fn lemma_sum_to_bound(arr: Seq<i64>, idx: nat)
    requires
        idx < arr.len(),
        forall |i: nat| 0 <= i < idx ==> arr.index(( i ) as int) >= 0,
    ensures
        sum_to(arr.subrange(0, ( idx ) as int)) as i128 + arr.index(( idx ) as int) as i128 <= i128::MAX,
        sum_to(arr.subrange(0, ( idx ) as int)) as i128 + arr.index(( idx ) as int) as i128 >= i128::MIN,
{
    // Here, you would add proof steps if needed, to show that the sum is within bounds.
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
            index <= arr.len(),
            arr.len() == arr.len(),
    {
        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            if index < arr.len() {
            }
        }
    }
    sum
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4