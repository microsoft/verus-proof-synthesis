
while index < arr.len()
    invariant
        index <= arr.len(),
        sum == sum_to(arr@.subrange(0, index as int)),
    {
        // loop body
    }


//             forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int)),
//   None: forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False