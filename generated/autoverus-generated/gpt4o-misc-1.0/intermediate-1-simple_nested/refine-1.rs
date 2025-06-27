
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
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] <= k + 2,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            sum <= 2 * i as i32,
            b.len() == N,
            N <= 0x3FFF_FFFF,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N,
                a[(i) as int] <= b[(i) as int] + 1,
                a[(i) as int] >= 0,
                forall|k: int| 0 <= k < i ==> a[k] <= k + 2,
                forall|k: int| k <= # [trigger] b[k] <= k + 1,
                j <= i,
                b.len() == N,
                N <= 0x3FFF_FFFF,
                b.len() == N,
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
