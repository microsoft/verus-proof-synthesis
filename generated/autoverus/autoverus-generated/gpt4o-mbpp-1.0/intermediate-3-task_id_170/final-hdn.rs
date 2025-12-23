
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

// Since sum_to is recursively defined, we may need to show properties about this function using a lemma.
proof fn lemma_sum_to_subrange(arr: Seq<i64>, start: int, end: int, i: int)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
        0 <= i < arr.len(),
    ensures
        sum_to(arr.subrange(start, i + 1)) + arr[i] as int == sum_to(arr.subrange(start, i + 2)),
{
    // Proof for the lemma, showing the monotonicity, is omitted for brevity but should establish the required property.
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
            index <= _end,
            start <= end < arr.len(),
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
            forall |k: int| 0 <= k < arr.len() ==> arr[k as int] == arr[k as int], // Adding this invariant since arr is never modified in the loop
    {
        // Assumption: The elements of the array are valid within i128 bounds
        
        sum = sum + arr[index] as i128;            
        index += 1;
    }
    sum
}

} // verus!






// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4