use vstd::prelude::*;
fn main() {}

verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall |i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    let ghost orig_v = v@;

    while n < length / 2
    invariant
        v.len() == length,
        0 <= n <= length / 2,
        forall |i: int| 0 <= i < n ==> v[i] == orig_v[length - 1 - i],
        forall |i: int| 0 <= i < n ==> v[length - 1 - i] == orig_v[i],
        forall |i: int| n <= i < length - n ==> v[i] == orig_v[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;

        proof {
            assert(forall |i: int| 0 <= i < n ==> v[i] == orig_v[length - 1 - i]);
            assert(forall |i: int| 0 <= i < n ==> v[length - 1 - i] == orig_v[i]);
            assert(forall |i: int| n <= i < length - n ==> v[i] == orig_v[i]);
        }
    }

    proof {
        assert forall |i:int| 0 <= i < length implies v[i] == orig_v[length - 1 - i] by {
            if i < length / 2 {
                assert(v[i] == orig_v[length - 1 - i]);
            } else {
                assert(length - 1 - i < length / 2);
                assert(v[i] == orig_v[length - 1 - i]);
            }
        }
    }
}
}
// Score: (1, 1)
// Safe: True