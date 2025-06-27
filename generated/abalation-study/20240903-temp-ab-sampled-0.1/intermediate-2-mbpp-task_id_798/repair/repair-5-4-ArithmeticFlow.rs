
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

proof fn lemma_sum_to_bound(arr: Seq<i64>)
    ensures
        sum_to(arr) <= arr.len() as int * i64::MAX as int,
{
    if arr.len() > 0 {
        lemma_sum_to_bound(arr.drop_last());
        assert(sum_to(arr.drop_last()) + arr.last() <= arr.len() as int * i64::MAX as int);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len() 
        invariant index <= arr.len(),
        invariant sum == sum_to(arr.subrange(0, index)@) as i128,
    {
        assert(sum + arr[index] as i128 <= arr.len() as i128 * i64::MAX as i128) by {
            lemma_sum_to_bound(arr.subrange(0, index + 1)@);
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
// Safe: False