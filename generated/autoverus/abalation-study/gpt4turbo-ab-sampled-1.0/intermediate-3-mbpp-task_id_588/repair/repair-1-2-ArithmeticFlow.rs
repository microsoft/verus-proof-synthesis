
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index <= arr.len(),
            arr.len() > 0,
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            max_val == max_rcur(arr@.subrange(0, (index) as int)),
            min_val <= max_val,
            min_val == min_rcur(arr@.subrange(0, (index) as int)),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    // Asserting that the calculation does not cause underflow/overflow.
    // This is based on the precondition that elements are in [i32::MIN/2, i32::MAX/2],
    // ensuring that the difference operation will remain within the bounds of i32.
    assert!(max_val >= min_val); // Note: This should always be true due to the loop invariant `min_val <= max_val`.

    max_val - min_val
}


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False