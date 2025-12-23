
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

proof fn lemma_sum_to_monotonic(i: nat, j: nat, arr: Seq<i64>)
    requires
        i <= j,
    ensures
        sum_to(arr.take((i as int).try_into().unwrap())) <= sum_to(arr.take((j as int).try_into().unwrap())),
    decreases j
{
    if i < j {
        lemma_sum_to_monotonic(i, (j - 1) as nat, arr);
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
            sum_to(arr@.take((index) as int)) <= sum_to(arr@),
    {
        assert(sum + (arr[( index ) as int] as i128) <= sum_to(arr@) as i128) by {
            let i = index as nat;
            let j = arr.len() as nat;
            lemma_sum_to_monotonic(i, j, arr@);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True