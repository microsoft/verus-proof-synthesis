
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

spec fn i64_to_i128(x: i64) -> i128 {
    x as i128
}

proof fn lemma_i128_addition_is_monotonic(x: i128, y: i128)
    ensures x <= x + y,
    decreases y
{
    // Simple proof for addition monotonicity
    if y > 0 {
        lemma_i128_addition_is_monotonic(x, ( y - 1 ) as i128);
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;
    while index < _end
        invariant
            0 <= start <= end < arr.len(),
            _end == end + 1,
            start <= index <= _end,
            sum_to(arr@.subrange(start as int, index as int)) == sum,
            forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr@[k], // Added invariant to cover every element in the array
    {
        let arr_elem = arr[index] as i128;
        assert(sum + arr_elem <= i128::MAX) by {
            lemma_i128_addition_is_monotonic(sum, arr_elem);
        };
        sum = sum + arr_elem;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4
// Safe: False