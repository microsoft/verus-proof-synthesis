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
            0 <= start <= end,
            start <= end < arr.len(),
            arr.len() == arr.len(),
            0 <= start,
            start <= end,
            _end == end + 1,
            index <= _end,
            start <= index <= end + 1,
            sum == sum_to(arr@.subrange(start as int, index as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            sum + arr[(index) as int] as i128 <= i128::MAX,
            sum >= i128::MIN, // Added by AI, for assertion fail
    {
        assert(sum + arr[index as int] as i128 <= i128::MAX);
        assert(sum >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;

        proof {
            assert(sum >= i128::MIN); // Adding proof assertion to ensure sum is not underflowing post update
        }
    }
    sum
}

}

//             assert(sum + arr[(index) as int] as i128 >= i128::MIN); // Added assertion to ensure no underflow
//   assertion failed: sum + arr[(index) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3
// Safe: True