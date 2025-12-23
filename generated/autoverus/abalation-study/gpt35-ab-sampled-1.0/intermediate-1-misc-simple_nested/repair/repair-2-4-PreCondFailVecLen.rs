
# ...

        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * N,
            sum >= N,
            a.len() == N, // Array length invariant
            i >= 0; // Array index not under bound invariant

# ...


//         sum = sum + a[i];
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False