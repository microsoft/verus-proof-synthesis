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
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length as int - i - 1],
            forall|i: int| 0 <= i < n ==> v[length as int - i - 1] == old(v)[i],
            n <= length / 2,
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
    
    proof {
        assert(forall|i: int| 0 <= i < length / 2 ==> v[i] == old(v)[length as int - i - 1]);
        assert(forall|i: int| length / 2 <= i < length ==> v[i] == v[length as int - i - 1]); // Changed from `old(v)` to `v`
        assert(forall|i: int| 0 <= i < length ==> v[i] == old(v)[length as int - i - 1]);
    }
}

}

//         assert(forall|i: int| length / 2 <= i < length ==> v[i] == old(v)[length as int - i - 1]);
//   assertion failed: forall|i: int| length / 2 <= i < length ==> v[i] == old(v)[length as int - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True