
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
            // Invariant now applies only to elements processed so far (up to 'index')
            forall|i: int| 0 <= i < index ==> max_val >= arr[i],
            forall|i: int| 0 <= i < index ==> min_val <= arr[i],
            index <= arr.len(),
            max_val >= arr[index - 1],
            min_val <= arr[index - 1],
            min_val <= max_val,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < # [trigger] arr[i] < i32::MAX / 2,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    //Assertion added to prevent overflow
    assert(max_val - min_val <= i32::MAX);

    max_val - min_val
}


//             forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i], // arr is never modified in the loop
//   None: forall|i: int| 0 <= i < arr.len() ==> max_val >= arr[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False