
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

proof fn lemma_sum_to_bound(seq: Seq<i64>)
    ensures
        forall |i: int| 0 <= i && i < seq.len() ==> int::MIN <= sum_to(seq.subrange(0, i)) <= int::MAX,
{
    decreases seq.len()
    if seq.len() > 0 {
        lemma_sum_to_bound(seq.drop_last());
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
            sum_to(arr@.subrange(0, index as int)) as i128 <= i128::MAX,
            sum_to(arr@.subrange(0, index as int)) as i128 >= i128::MIN,
            index < arr.len(),
            arr.len() == arr.len(),
    {
        let current_value = arr[index] as i128;

        // Assert to ensure no overflow or underflow
        assert(sum + current_value <= i128::MAX);
        assert(sum + current_value >= i128::MIN);

        sum = sum + current_value;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False