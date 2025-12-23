
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

proof fn lemma_sum_bounded(i: u64, sum: i128, max_i128: i128, min_i128: i128)
    requires
        sum >= min_i128,
        sum <= max_i128,
        i <= arr.len(),
    ensures
        sum + arr[i as nat] <= max_i128 &&
        sum + arr[i as nat] >= min_i128,
    decreases i
{
    if i > 0 {
        lemma_sum_bounded(i - 1, sum, max_i128, min_i128);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    let max_i128 = i128::max_value();
    let min_i128 = i128::min_value();
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,
            sum >= min_i128,
            sum <= max_i128,
    {
        assert(sum + arr[index] as i128 <= max_i128 && sum + arr[index] as i128 >= min_i128) by {
            // This lemma ensures that the sum after adding the current element is still within i128 bounds
            lemma_sum_bounded(index, sum, max_i128, min_i128);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False