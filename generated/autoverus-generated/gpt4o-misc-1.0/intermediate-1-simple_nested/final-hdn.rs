use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= #[trigger] b[k] <= k + 1,
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
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < b.len() ==> b[k] <= k + 1, // ensuring the invariant covers all elements in 'b'
            i <= N as usize,
            b.len() == N,
            N <= 0x3FFF_FFFF,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= k + 1, // ensuring the invariant covers all elements in 'b'
                j <= i,
                b.len() == N,
                N <= 0x3FFF_FFFF,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3