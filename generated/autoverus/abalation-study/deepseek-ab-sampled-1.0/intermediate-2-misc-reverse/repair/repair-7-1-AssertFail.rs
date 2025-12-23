
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let old_v = old(v);
    let length = v.len();
    let mut n: usize = 0;

    while n < length / 2
    invariant
        0 <= n <= length / 2,
        forall|i: int| 0 <= i < n ==> v[i] == old_v[length - i - 1],
        forall|i: int| n <= i < (length - n) ==> v[i] == old_v[i],
        n <= length,
        v.len() == length,
        v.len() == old_v.len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;

        proof {
            for i in 0..n {
                assert(v[( i ) as int] == old_v[length - i - 1]);
            }
            for i in n..( (length - n) ) as usize {
                assert(v[( i ) as int] == old_v[( i ) as int]);
            }
        }
    }

    proof {
        assert(n == length / 2);
        if length % 2 == 0 {
            for i in 0..n {
                assert(v[( i ) as int] == old_v[length - i - 1]);
            }
            for i in n..length {
                assert(v[( i ) as int] == old_v[length - i - 1]);
            }
        } else {
            for i in 0..n {
                assert(v[( i ) as int] == old_v[length - i - 1]);
            }
            assert(v[( n ) as int] == old_v[( n ) as int]);
            for i in n+1..( length ) as int {
                assert(v[i] == old_v[length - i - 1]);
            }
        }
        assert(forall|i: int| 0 <= i < old_v.len() ==> v[i] == old_v[old_v.len() - i - 1]);
    }
}
}












//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False