
while (i < N as usize)
    invariant
        N < 1000,
        N > 0,
        a.len() == N as usize,
        i <= N as usize,
        0 <= i, // Added by AI
        i < N as usize, // Added by AI
        a[i as int] >= 0, // Added by AI
        a[i as int] <= 2, // Added by AI
        sum[0] + a[i as int] >= 0, // Added by AI
        sum[0] + a[i as int] <= 2 * (i + 1), // Added by AI
{
    a.set(i, (i % 3) as i32);
    i = i + 1;
}

i = 0;
assert(old(sum)[0] + a[i as int] <= 2 * (i + 1)); // Added by AI
while (i < N as usize)
    invariant
        N < 1000,
        N > 0,
        a.len() == N as usize,
        i <= N as usize,
        old(sum)[0] + a[i as int] <= 2 * (i + 1), // preserving the previous invariant
        sum.len() == 1, // Added by AI
{
    if (i == 0) {
        sum.set(0, 0);
    } else {
        sum.set(0, sum[0] + a[i]);
    }
    i = i + 1;
    assert(old(sum)[0] + a[i as int] <= 2 * (i + 1)); // Added by AI
}


//             sum.len() == 1,
//   None: sum.len() == 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False