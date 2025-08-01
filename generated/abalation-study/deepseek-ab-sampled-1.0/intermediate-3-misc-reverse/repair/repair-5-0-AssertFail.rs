
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
    if length == 0 {
        return;
    }
    let mut n: usize = 0;
    while n < length / 2
        invariant
            old(v).len() == length,
            v.len() == length,
            n <= length / 2,
            (n as int) <= length as int,
            prove_contextually_during_initialization(),
        {
            proof {
                let n_int = n as int;
                assert(forall|k: int| 0 <= k < n_int ==> v[k] == old(v)[length - 1 - k]);
                assert(forall|k: int| n_int <= k < length - n_int ==> v[k] == old(v)[k]);
                assert(forall|k: int| (length - n_int) <= k < length ==> 
                    exists|x: int| x == k ==> v[x] == old(v)[x]);
            }
            
            let x = v[n];
            let y = v[length - 1 - n];
            
            v.set(n, y);
            v.set(length - 1 - n, x);
            n = n + 1;
            
            proof {
                let new_n = n + 1;
                assert(forall|k: int| 0 <= k < new_n as int ==> 
                    v[k] == old(v)[length - 1 - k]);
                assert(forall|k: int| new_n as int <= k < length - new_n as int ==> 
                    v[k] == old(v)[k]);
                assert(forall|k: int| (length - new_n as int) <= k < length ==> 
                    exists|x: int| x == k ==> v[x] == old(v)[x]);
            }
        }
    proof {
        let final_n = length / 2;
        assert(forall|k: int| 0 <= k < final_n as int ==> 
            v[k] == old(v)[length - 1 - k]);
        assert(forall|k: int| final_n as int <= k < length - final_n as int ==> 
            v[k] == old(v)[k]);
        assert(forall|k: int| (length - final_n as int) <= k < length ==> 
            exists|x: int| x == k ==> v[x] == old(v)[x]);
    }
}

}


//             assert(forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]);
//   assertion failed: forall|k: int| (length - (n as int)) <= k < length ==> v[k] == old(v)[k]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False