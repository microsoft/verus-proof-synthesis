
// ... previous code ...

    i = 0;
    // Explicitly assert c's length before the loop
    assert!(c.len() == N as usize);
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            c.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> c[(j) as int] == 1,
            sum[0] + c[( i ) as int] <= 3 * N + i as i32,
    {
        c.set(i, 1);
        i = i + 1;
    }

// ... rest of the code ...


//             c.len() == N,
//   None: c.len() == N

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False