use vstd::prelude::*;
fn main() {}
verus! {

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= # [trigger] b[k] <= k + 1,
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
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            a.len() == N as usize,
            b.len() == N as usize,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * N,
            sum >= N,
            sum >= 0,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize,
                forall|k: int| 0 <= k < j ==> a[k] == b[k] + 1,
                j <= i,
                sum >= 0,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 10