
use vstd::prelude::*;
fn main() {}

verus!{
    fn reverse(v: &mut Vec<u64>)
        ensures
            v.len() == old(v).len(),
            forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
    {
        let length = v.len();
        let mut n: usize = 0;
        while (n < length / 2)
            invariant
                0 <= n < length,
                n <= length / 2,
                forall |i: usize| i < n ==> v[( i ) as int] == old(v)[length - 1 - i] && v[length - 1 - i] == old(v)[( i ) as int],
                v.len() == length,
        {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);
            n = n + 1;
        }
    }
}



// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1