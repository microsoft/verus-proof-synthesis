
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
            0 <= n <= length / 2,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| (length / 2) <= i < length - i as usize ==> v[i] == old(v)[length - i - 1],
            forall|i: int| n <= i < (length as int) - n ==> v[i] == old(v)[i],
            n <= length,
            v.len() == length,
            v.len() == old(v).len(),
    {
        proof {
            let lower = n;
            let upper = length - 1 - n;
            assert(lower < upper); // Maintain loop invariant before modification
            assert(old(v)[( lower ) as int] == old(v)[length - 1 - lower]);
        }
        
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;
        
        proof {
            // Verify the invariants hold after swap
            assert(forall|i: int| 0 <= i < n + 1 ==> v[i] == old(v)[length - i - 1]);
            assert(forall|i: int| (length as int) - (n + 1) <= i < length ==> v[i] == old(v)[length - i - 1]);
            assert(forall|i: int| n + 1 <= i < (length as int) - (n + 1) ==> v[i] == old(v)[i]);
        }
    }
    
    proof {
        // Final verification step after loop completes
        assert(forall|i: int| 0 <= i < length as int ==> v[i] == old(v)[length - i - 1]);
    }
}

}



//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False