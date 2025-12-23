
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
        assert(sum_to(arr.subrange(0, i as int)) <= sum_to(arr.subrange(0, (j - 1) as int)) + arr[(j - 1) as int]);
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
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
    {
        // Adding an assertion to check for overflow/underflow
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@) as i128) by {
            lemma_monotonic(arr@, index, arr.len());
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