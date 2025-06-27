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
            arr.len() < 100,
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            sum == sum_to(arr@.subrange(0, (index) as int)),
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5