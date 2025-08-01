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

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            arr.len() == arr@.len(),
    {
        // Assert that adding the next element won't cause overflow

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2