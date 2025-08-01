
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * N,
            sum >= N,
            // Loop invariant for array a
            a.len() == N,
            i < N as usize


//         sum = sum + a[i];
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False