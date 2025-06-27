use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    
    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 4,
            forall|j: int| i as int <= j < N as int ==> a[j] == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    
    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 4 * i as i32,
            a.len() == N,
            forall|j: int| j < i as int ==> a[j] == 4,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4