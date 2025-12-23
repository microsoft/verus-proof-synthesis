
use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_to(arr: Seq<i64>) -> i128
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last() as i128
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut i: usize = 0;
    let mut s: i128 = 0;

    while (i < arr.len())
        invariant
            0 <= i <= arr.len(),
            s == sum_to(arr@.take(i as int)),
    {
        s = s + arr[i] as i128;
        i = i + 1;
    }

    s
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1