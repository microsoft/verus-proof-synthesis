use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum(arr: &Vec<i64>) -> (total: i128)
    ensures
        sum_to(arr@) == total,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |i: int| 0 <= i < index ==> sum == sum_to(arr@.take(index as int)) as i128,
            sum_to(arr@) == sum_to(arr@.take(index as int)) + sum_to(arr@.skip(index as int)),
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1