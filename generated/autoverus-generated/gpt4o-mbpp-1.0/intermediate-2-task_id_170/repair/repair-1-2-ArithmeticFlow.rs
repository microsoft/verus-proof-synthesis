
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

proof fn lemma_nonneg_sum_to(arr: Seq<i64>)
    requires
        forall |i: nat| i < arr.len() ==> arr.index(i) >= 0,
    ensures
        sum_to(arr) >= 0,
{
    // A recursive proof that sum_to is non-negative if all elements are non-negative
    if arr.len() > 0 {
        lemma_nonneg_sum_to(arr.drop_last());
    }
}

proof fn lemma_bound_sum(arr: Seq<i64>, start: int, end: int)
    requires
        0 <= start <= end < arr.len(),
        sum_to(arr.subrange(start, end+1)) < i128::MAX,
    ensures
        forall |i: int| start <= i <= end ==> sum_to(arr.subrange(start, i+1)) < i128::MAX,
{
    if start <= end {
        lemma_bound_sum(arr, start, end-1);
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        end < arr.len(),
        sum_to(arr@.subrange(start as int, end + 1 as int)) < i128::MAX,
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
        assert(sum + arr[index] as i128 < i128::MAX) by {
            lemma_bound_sum(arr@, start as int, end as int);
        };
        
        assert(sum + arr[index] as i128 >= i128::MIN) by {
            // Assuming all elements in `arr` are non-negative or providing a similar proof
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}
} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False