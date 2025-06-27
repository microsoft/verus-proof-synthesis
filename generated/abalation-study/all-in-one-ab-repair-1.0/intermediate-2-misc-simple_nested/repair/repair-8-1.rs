
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N as nat,
        b.len() == N as nat,
        N > 0,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < N as usize
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N as nat,
            forall|k: int| 0 <= k < i as int ==> a[k as nat] == b[k as nat] + 1 - k as i32,
            i <= N as usize,
            old(a).len() == N as nat,
            sum <= 2 * i as i32,
            a.len() == N as nat,
    {
        proof {
            assert(N <= 0x3FFF_FFFF);
            assert(b.len() == N as nat);
            assert(forall|k: int| 0 <= k < i as int ==> a[k as nat] == b[k as nat] + 1 - k as i32);
            assert(i <= N as usize);
            assert(old(a).len() == N as nat);
            assert(sum <= 2 * i as i32);
            assert(a.len() == N as nat);
        }

        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                a[i] == b[i] + 1 - j as i32,
                b.len() == N as nat,
                forall |k: int| 0 <= k < i as int ==> a[k as nat] == b[k as nat] + 1 - k as i32,
                j <= i,
                old(a).len() == N as nat,
                a.len() == N as nat,
        {
            proof {
                assert(N <= 0x3FFF_FFFF);
                assert(a[i] == b[i] + 1 - j as i32);
                assert(b.len() == N as nat);
                assert(forall |k: int| 0 <= k < i as int ==> a[k as nat] == b[k as nat] + 1 - k as i32);
                assert(j <= i);
                assert(old(a).len() == N as nat);
                assert(a.len() == N as nat);
            }

            a.set(i, a[i] - 1);
            j += 1;
        }
        sum += a[i];
        i += 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzzamc9ru`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 12
// Safe: False