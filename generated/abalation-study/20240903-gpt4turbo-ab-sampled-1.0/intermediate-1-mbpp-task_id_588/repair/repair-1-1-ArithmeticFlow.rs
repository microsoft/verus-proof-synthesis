
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    while index < arr.len()
        invariant
            1 <= index,
            arr.len() > 0,
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < index ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
            index <= arr.len(),
            max_val >= max_rcur(arr@),
            min_val <= max_val,
            min_val <= min_rcur(arr@),
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    // Ensure the difference doesn't overflow an i32.
    assert!(max_val as i64 - min_val as i64 <= i32::MAX as i64);
    max_val - min_val
}


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False