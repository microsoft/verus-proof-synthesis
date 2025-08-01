
        invariant
            b.len() == N,
            a.len() == N,
            i <= N as usize,
            forall|k: int| k <= N - 1,
            sum <= 2 * N,
            sum >= N,
            i < N as usize,
            old(a).len() == N,
            a.len() == N,
            i <= N as usize,
            forall|k: int| k <= N - 1,
            i <= N as usize,
            a.len() == N


//         sum = sum + a[i];
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False