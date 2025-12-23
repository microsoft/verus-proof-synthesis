use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 0,
            i <= N,
            sum.len() == 1,
            N > 0,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    proof {
        assert((sum[0] == 0 && i == 0) || (sum[0] == 0 && i > 0));
    } // Added by AI
    while (i < N as usize)
        invariant
            (sum[0] == 0 && i == 0) || (sum[0] == 0 && i > 0),
            a.len() == N,
            forall |k: int| 0 <= k < a.len() ==> a[k] == a[k], // Adding invariant for `a` because it is not modified in this loop
            i <= N,
            sum.len() == 1,
            N > 0,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
        proof {
            assert((sum[0] == 0 && i == 0) || (sum[0] == 0 && i > 0));
        } // Added by AI
    }
}

} // verus!

//             assert((sum[0] == 0 && i == 0) || (sum[0] == 0 && i > 0));
//   assertion failed: (sum[0] == 0 && i == 0) || (sum[0] == 0 && i > 0)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: True