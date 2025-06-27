
while (index < arr.len() - 1)
    invariant
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= # [trigger] arr[i] + 1 < i32::MAX),
        index < arr.len(),
        forall|i: int, j: int| 0 <= i < j && j <= index && j < arr.len() ==> (arr[i] + 1 == arr[j]),
{
    if (arr[index] + 1 != arr[index + 1]) {
        return false;
    }
    index += 1;
}


//             forall|i: int, j: int| 0 <= i < j <= index + 1 && j < arr.len() ==> (arr[i] + 1 == arr[j]),
//   None: forall|i: int, j: int| 0 <= i < j <= index + 1 && j < arr.len() ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False