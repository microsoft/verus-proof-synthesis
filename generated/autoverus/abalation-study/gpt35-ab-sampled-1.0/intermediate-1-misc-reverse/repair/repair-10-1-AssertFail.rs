
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
    proof {
        assert(forall|i: int| length as usize / 2 <= i < old(v).len() as usize  ==> v[i] == old(v)[old(v).len() as usize - i - 1]);
    }
    while n < length / 2
        invariant
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[old(v).len() - i - 1],
            forall|i: int|
                length as usize / 2 <= i < old(v).len() as usize ==> v[i] == old(v)[old(
                    v.len() as usize - i - 1),
                len() as usize - i - 1],
            forall|i: int| n <= i < old(v).len() - n ==> v[i] == old(v)[i],
            n <= length / 2,
            v.len() == old(v).len(),
    {
        let x = v[n];
        let y = v[length - 1 - n];
        // The array v is modified through v.set() in this loop, so the loop invariant remains unchanged
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
        proof {
            assert(forall|i: int| length as usize / 2 <= i < old(v).len() as usize  ==> v[i] ==  old(v)[old(v).len() as usize - i - 1]);
        }
    }
}

} // verus!


//         assert(forall|i: int| length as usize / 2 <= i < old(v).len() as usize  ==> v[i] == old(v)[old(v).len() as usize - i - 1]);
//   assertion failed: forall|i: int| length as usize / 2 <= i < old(v).len() as usize  ==> v[i] == old(v)[old(v).len() as usize - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False