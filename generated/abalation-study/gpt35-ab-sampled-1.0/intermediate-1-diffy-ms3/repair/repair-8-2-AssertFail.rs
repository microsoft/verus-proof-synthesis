
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
            a[0] == 0,
            a[( i ) as int] == (i % 3) as i32 || a[( i ) as int] == 0,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(sum[0] >= 0 && sum[0] <= 2 * N);
    }
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
            sum[0] + a[(i) as int] >= 0,
            sum[0] + a[(i) as int] <= 2 * N,
            sum[0] <= 2 * N,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
    proof {
        assert(sum[0] >= 0 && sum[0] <= 2 * N);
        assert(sum[0] <= 2 * N);
    }
}

} // verus!




//         assert(sum[0] >= 0 && sum[0] <= 2 * N); // Added by AI
//   assertion failed: sum[0] >= 0 && sum[0] <= 2 * N

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 8
// Safe: True