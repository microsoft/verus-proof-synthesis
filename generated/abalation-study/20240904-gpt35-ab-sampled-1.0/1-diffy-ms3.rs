
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
            // The array 'a' is modified in the loop using a.set(), so the loop invariant remains unchanged.
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(sum[0] >= 0 && sum[0] <= 2 * N);
    } // Added by AI
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
            // The array 'a' is never modified in this loop, and the invariant already covers every element in the array.
            sum[0] + a[(i) as int] >= 0, // Added by AI
            sum[0] + a[(i) as int] <= 2 * N, // Added by AI
            sum[0] <= 2 * N, // Added by AI
            sum[0] >= 0, // Added by AI
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
    proof {
        assert(sum[0] >= 0 && sum[0] <= 2 * N); // Added by AI
    } // Added by AI
}

} // verus!

// Score: (2, 3)
// Safe: True