

use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            old(v).len() == length,
            v.len() == length,
            n <= length / 2,
            (n as int) <= length as int,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1],
            forall|i: int| (n as int) <= i < (length as int) - n as int ==> v[i] == old(v)[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        
        proof {
            assert(forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1]);
            assert(forall|i: int| n as int <= i < (length as int) - n as int ==> v[i] == old(v)[i]);
        }
        
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    proof {
        let remaining = length as int - 2 * n as int;
        assert(forall|i: int| 0 <= i < n as int ==> v[i] == old(v)[length as int - i - 1]);
        assert(forall|i: int| n as int <= i < remaining ==> v[i] == old(v)[i]);
        assert(length as int - n as int == n as int + remaining);
    }
}

}

//         assert(length as int - n as int == n as int + remaining);
//   assertion failed: length as int - n as int == n as int + remaining

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True