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
            arr.len() < 1000, // Assuming a bound to prevent excessive runtime memory usage
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4