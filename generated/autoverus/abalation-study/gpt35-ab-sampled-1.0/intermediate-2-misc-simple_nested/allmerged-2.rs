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
            0 <= i <= N as usize,
            N <= 0x3FFF_FFFF,
            N <= sum <= 2 * N,
            a.len() == N,
            a.len() == N as usize,
            b.len() == N,
            b.len() == N as usize,
            forall|k: int| k < i ==> a[k] == b[k] + 1,
            forall|k: int| k < i ==> a[k] == b[k] - 1,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1,
            i <= N as usize,
            sum <= i as i32,
            sum >= 0,
            sum >= 0 && sum <= i as i32 + 1,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= i <= N as usize,
                0 <= j <= i,
                N <= 0x3FFF_FFFF,
                N <= sum <= 2 * N,
                a.len() == N,
                a.len() == N as usize,
                a[(i) as int] == b[(i) as int] + 1 - j as i32,
                b.len() == N,
                forall|k: int| k < i ==> a[k] == b[k] + 1,
                forall|k: int| k < j ==> a[(i) as int] + j - k == b[k] + 1,
                forall|k: int| k < j ==> a[k] == b[k] - 1,
                j <= i,
                sum >= 0 && sum <= i as i32 + 1,
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 9