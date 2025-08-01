
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, new_val: i64)
    requires
        arr.extended_length() <= arr.extended_length() + 1,
    ensures
        sum_to(arr.push(new_val)) == sum_to(arr) + new_val,
{
    // Recursively ensure the bounds
    if arr.len() > 0 {
        lemma_sum_to_monotonic(arr.drop_last(), arr.last());
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
            sum_to(arr@.subrange(0, index as int)) == sum as int,
            index <= arr.len(),
            arr.len() == arr.len(),  // Invariant specifying the length of the array
    {
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_monotonic(arr.subrange(0, index as int), arr[index]);
        };
        assert(sum + arr[index] as i128 >= i128::MIN) by {
            lemma_sum_to_monotonic(arr.subrange(0, index as int), arr[index]);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: True