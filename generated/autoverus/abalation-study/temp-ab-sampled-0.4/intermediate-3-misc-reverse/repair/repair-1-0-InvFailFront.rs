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
        assert(n < length / 2); // Added by AI
    }
    while n < length / 2
        invariant
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| 0 <= i < n ==> v[length - i - 1] == old(v)[i],
            n <= length / 2,
            v.len() == length,
            n < length / 2,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n = n + 1;
    }
}

} // verus!

//             n < length / 2,
//   None: n < length / 2

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True