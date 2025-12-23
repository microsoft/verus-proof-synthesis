
            invariant
                a.len() == N,
                i <= N,
                sum.len() == 1,
                sum.index(0) <= N,
                i >= 0,


//                 sum.set(0, sum[0] + a[i]);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: sum[0]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False