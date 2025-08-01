
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            i <= N,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: usize| 0 <= k < N as usize ==> a[(k) as int] == 1,
            forall|k: usize| 0 <= k < i ==> b[(k) as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N + i as i32,
            sum[0] <= N + (i as i32),
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
        proof {
            assert(sum[0] - N <= 2 * (i as i32));
        }
    }
}


//             sum[0] <= i as i32,
//   None: sum[0] <= i as i32

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False