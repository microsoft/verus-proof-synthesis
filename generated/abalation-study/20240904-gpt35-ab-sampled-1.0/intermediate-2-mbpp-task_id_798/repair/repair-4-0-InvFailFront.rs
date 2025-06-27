
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

    assert(0 <= index < arr.len()) by { } // Added by AI
    while index < arr.len()
        invariant
            0 <= index < arr.len(), // The array arr is never modified in the loop
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by { }
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN) by { }
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//             0 <= index < arr.len(), // The array arr is never modified in the loop
//   None: index

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True