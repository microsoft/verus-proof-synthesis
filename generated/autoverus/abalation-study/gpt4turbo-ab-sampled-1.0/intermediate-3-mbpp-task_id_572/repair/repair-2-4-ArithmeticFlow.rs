
if (arr[index] == key) {
    // Safety assertion to ensure counter will not overflow.
    assert(counter < usize::MAX);
    counter += 1;
}


//             counter += 1;
//   None: counter += 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False