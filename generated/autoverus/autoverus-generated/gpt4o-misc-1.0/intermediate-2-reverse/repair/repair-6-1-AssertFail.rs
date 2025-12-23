use vstd::prelude::*;
fn main() {}

verus! {

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            // No changes since v is modified using v.set() in the loop
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - 1 - i],
            forall|i: int| 0 <= i < n ==> v[length - 1 - i] == old(v)[i],
            n <= length / 2,
            v.len() == length,
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;
    }
    proof {
        let adjusted_length = length;
        assert(forall|i: int| 0 <= i < adjusted_length ==> v[i] == old(v)[adjusted_length - 1 - i]);
    }
}

} // verus!

//         assert(forall|i: int| 0 <= i < adjusted_length ==> v[i] == old(v)[adjusted_length - 1 - i]);
//   assertion failed: forall|i: int| 0 <= i < adjusted_length ==> v[i] == old(v)[adjusted_length - 1 - i]

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False