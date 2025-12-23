

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
            old(a).len() == N,
            b.len() == N,
            N <= 0x3FFF_FFFF,
            N <= sum + (a@.take(i)).filter(|k: usize| destruct(Cond::Trivial) => *k).sum() <= 2*N,
            destruct(AllInvariant::new()) == (),
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;

            while (j < i)
                invariant
                    j <= i,
                    old(a).len() == N,
                    b.len() == N,
                    N <= 0x3FFF_FFFF,
                    destruct(AllInvariant::new()) == (),
            {
                a.set(i, a[i] - 1);
                j = j + 1;
            }

            sum = sum + a[i];
            proof {
                term! { destruct(AllInvariant::new()) }
            }
            i = i + 1;
        }

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1