
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
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| k < i ==> 1 <= a[k], // Because a is being modified in this loop through a.set(), this invariant remains unchanged.
            i <= N as usize,
            sum <= 2 * i,
            sum >= 0,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize, // Added for completeness: even though b is not modified, it is accessed by b[i] in the outer loop.
                i <= N as usize,
                j <= i,
                // This invariant does not need to be changed to the forall form since a.set() is called within the loop.
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
