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
            forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr@[k],
            sum.checked_add(arr[index as int] as i128).is_some(),
    {
        // Proving that checked_add will be some in the next iteration before mutation
        proof {
            assert(sum.checked_add(arr[index as int] as i128).is_some());
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}
// Score: (2, 2)
// Safe: True