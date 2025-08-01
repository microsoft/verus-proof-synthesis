
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    i = 0;
    let mut temp_sum: i32 = 0; // Added by AI
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N as usize,
            temp_sum <= 3 * N, // Updated invariant
            N > 0,
            sum[0] <= 3 * N, // Added by AI
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            sum[0] == temp_sum, // Added by AI
    {
        temp_sum = temp_sum + a[i];
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    sum.set(0, temp_sum); // Updated by AI
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        b.set(i, 1);
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    i = 0;
    let mut temp_sum2: i32 = 0; // Added by AI
    while (i < N as usize)
        invariant
            b.len() == N,
            i <= N as usize,
            temp_sum2 <= 3 * N, // Updated invariant
            N > 0,
            sum[0] <= 3 * N, // Added by AI
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            sum[0] == temp_sum + temp_sum2, // Added by AI
    {
        temp_sum2 = temp_sum2 + b[i];
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    sum.set(0, temp_sum + temp_sum2); // Updated by AI
    i = 0;
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        c.set(i, 1);
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    i = 0;
    let mut temp_sum3: i32 = 0; // Added by AI
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N as usize,
            temp_sum3 <= 3 * N, // Updated invariant
            N > 0,
            sum[0] <= 3 * N, // Added by AI
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            sum[0] == temp_sum + temp_sum2 + temp_sum3, // Added by AI
    {
        temp_sum3 = temp_sum3 + c[i];
        i = i + 1;
        proof {
            assert(i < N as usize);
        }
    }
    sum.set(0, temp_sum + temp_sum2 + temp_sum3); // Updated by AI
}

} // verus!


//             sum[0] + a[i as int] <= 3 * N, // Updated invariant
//   None: sum[0] + a[i as int] <= 3 * N

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False