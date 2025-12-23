

use vstd::prelude::*;

fn main() {}

verus! {
    fn reverse(v: &mut Vec<u64>)
        ensures
            v.len() == old(v).len(),
            forall |i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
    {
        let length = v.len();
        let mut n: usize = 0;

        #[verifier::loop_invariant]
        while n < length / 2
            invariant
                v.len() == length,
                n <= length / 2,
                forall |i: int| 0 <= i < n as int ==> v[i] == old(v)[length - 1 - i as usize],
        {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);

            n += 1;
        }

        assert(v.len() == length);
        assert(forall |i: int| 0 <= i < length as int ==> v[i] == old(v)[length - 1 - i as usize]);
    }
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1