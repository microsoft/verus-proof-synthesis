
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
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
            v.len() == length,
            n <= length,
            n <= length / 2,
        {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);
            n = n + 1;
            proof {
                let i = n as int - 1;
                let j = (length as int) - i - 1;
                assert(v[i as int] == old(v)[j as int]);
                assert(v[j as int] == old(v)[i as int]);
            }
        }
    proof {
        let len = length as int;
        assert(forall|i: int| 0 <= i < len ==> 
            if i < len / 2 then 
                v[i] == old(v)[len - i - 1] 
            else if i == len / 2 then 
                v[i] == old(v)[i] 
            else 
                v[i] == old(v)[len - i - 1]);
        
        // Now, since both halves satisfy the reversal property, combine them into a single assertion
        assert(forall|i: int| 0 <= i < len ==> v[i] == old(v)[len - i - 1]);
    }
}
}


//         assert(forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]);
//   assertion failed: forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False