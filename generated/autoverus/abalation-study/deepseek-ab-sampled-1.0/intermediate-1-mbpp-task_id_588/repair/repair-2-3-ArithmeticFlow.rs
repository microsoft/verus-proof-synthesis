
// ... same as before

while index < arr.len()
    invariant
        0 <= index <= arr.len(),
        max_val == max_rcur(Seq::new((index) as nat, |i: int| arr[i as int] as i32)),
        min_val == min_rcur(Seq::new((index) as nat, |i: int| arr[i as int] as i32)),
        forall|i: int| 0 <= i < index ==> i32::MIN / 2 < arr[i],
        forall|i: int| 0 <= i < index ==> arr[i] < i32::MAX / 2,
{
    if (arr[index] <= min_val) {
        min_val = arr[index];
    } else if (arr[index] > max_val) {
        max_val = arr[index];
    }
    index += 1;
}

// Assertion to prevent overflow before subtraction
assert(max_val - min_val <= i32::MAX);

max_val - min_val


//     max_val - min_val
//   None: max_val - min_val

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False