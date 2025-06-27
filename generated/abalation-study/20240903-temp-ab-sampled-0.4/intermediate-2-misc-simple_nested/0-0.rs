use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize) 
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32,
            forall |k:int| k <= b[k] <= k + 1,
            sum == (0..i).fold(0, |acc, k| acc + a[k]),
            N <= sum + (N - i as i32) <= 2 * N,
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a.len() == N,
                b.len() == N,
                forall |k:int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32,
                forall |k:int| k <= b[k] <= k + 1,
                a[i] == b[i] + 1 - j as i32,
                sum == (0..i).fold(0, |acc, k| acc + a[k]),
                N <= sum + (N - i as i32) <= 2 * N,
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
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3