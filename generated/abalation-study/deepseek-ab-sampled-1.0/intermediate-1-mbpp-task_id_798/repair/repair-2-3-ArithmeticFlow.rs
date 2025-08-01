
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

trust fn i128_max() -> i128 {
    i128::MAX
}

trust fn i128_min() -> i128 {
    i128::MIN
}

proof fn lemma_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        sum_to(Seq::from(src!(()), i as int..j as int)) <= sum_to(Seq::from(src!(()), 0..j as int)),
    decreases j
{
    if i < j {
        lemma_monotonic(i, (j - 1) as nat);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    requires
        sum_to(arr@) <= i128_max() as int,
        sum_to(arr@) >= i128_min() as int,
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
            sum <= i128_max(),
            sum >= i128_min(),
    {
        assert(sum <= (i128_max() - arr[index] as i128));
        assert(sum >= (i128_min() - arr[index] as i128));
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False