use vstd::prelude::*;
fn main() {}
verus! {
fn fun(v: &mut Vec<usize>, a: &mut Vec<usize>, k: usize, N: i32)
    requires
        0 < k < 1000,
        old(v).len() == old(a).len() == N,
        0 < N < 1000,
    ensures
        forall |j:int| 0<= j <v.len() ==> v[j] == k + j,
{

    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            a.len() == N,
            v.len() == N,
            forall |j:int| 0<= j < i ==> a[j] == j,
    {
        a.set(i, i);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 < k < 1000,
            v.len() == N,
            a.len() == N,
            forall |j:int| 0<= j < N ==> a[j] == j,
            forall |j:int| 0<= j <i ==> v[j] == k + j,
    {
        v.set(i, k + a[i]);
        i = i + 1;
    }

}
}
