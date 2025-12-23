
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

proof fn lemma_bound_sum_to(arr: Seq<i64>)
    ensures
        forall |i: nat| 0 <= i && i < arr.len() ==> sum_to(arr.subrange(0, i)) + arr.index(i) as int <= sum_to(arr)
{
    decreases arr.len();
    if arr.len() > 0 {
        let last = arr.last();
        lemma_bound_sum_to(arr.drop_last());
        assert(forall |i: nat| 0 <= i && i < arr.len() - 1 ==> 
            sum_to(arr.subrange(0, i)) + arr.index(i) as int <= sum_to(arr.drop_last()));
        assert(forall |i: nat| 0 <= i && i == arr.len() - 1 ==> 
            sum_to(arr.drop_last()) + last as int == sum_to(arr));
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
            arr.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(),
            arr.len() == arr.len(),
    {
        assert(sum + arr[index] as i128 <= sum_to(arr@) as i128) by {
            lemma_bound_sum_to(arr@);
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False