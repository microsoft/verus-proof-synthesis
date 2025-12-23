use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            N <= 0x3FFF_FFFF,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32,
            sum <= 2 * i as i32,
            N <= 0x3FFF_FFFF, // Repeated invariant
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                N <= 0x3FFF_FFFF,
                a.len() == N,
                b.len() == N,
                forall|k: int| 0 <= k < j ==> a[k] == b[k] + 1 - k as i32, // Corrected invariant
                a[( i ) as int] == b[( i ) as int] + 1 - j as i32,
                N <= 0x3FFF_FFFF, // Repeated invariant
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        proof {
            assert(forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32);
        }
        i = i + 1;
        proof {
            assert(forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32); // Corrected the assertion
        }
    }
    sum
}

}



//             assert(forall|k: int| 0 <= k <= i ==> a[k] == b[k] + 1 - k as i32); // Moved to after increment of i
//   assertion failed: forall|k: int| 0 <= k <= i ==> a[k] == b[k] + 1 - k as i32

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False