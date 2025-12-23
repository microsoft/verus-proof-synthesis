use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<usize>, N: usize)
    requires
        N < 100,
        old(a).len() == N,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == 2,
{
    let mut i: usize = 0;

    while (i < N)
    {
        a.set(i, 0);
        i = i + 1;
    }

    i = 0;
    while (i < N)
    {
        a.set(i, a[i] + 2);
        i = i + 1;
    }
}
}
