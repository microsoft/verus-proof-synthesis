
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
                forall|j: int| (0 <= j < n as int) ==> v[j] == old(v)[length - j - 1],
                forall|j: int| (n as int <= j < (length - n) as int) ==> v[j] == old(v)[j],
                n <= length,
                length == old(v).len(),
                v.len() == length,
        {
            let x = v[n];
            let y = v[length - 1 - n];
            v.set(n, y);
            v.set(length - 1 - n, x);
            n = n + 1;
        }
        proof {
            let length_ghost = length as int;
            let mid = length_ghost / 2;
            assert(forall|k: int| 0 <= k < mid ==> 
                       v[k] == old(v)[length_ghost - k - 1]) by {
                // For each k < mid, since n increments up to mid, the loop ensures that after each iteration,
                // v[k] == old(v)[length - k - 1] for all k < n.
                // After the loop completes, n has reached mid, so the assertion holds for 0 <= k < mid.
                x_suffices! {
                    forall|k: int| 0 <= k < mid ==> {
                        have h: 0 <= k < n as int by assumption;
                        have h2: v[k] == old(v)[length_ghost - k - 1] by <; h;
                    }
                }
            };
            assert(forall|k: int| 0 <= k < length_ghost ==> 
                       v[k] == old(v)[length_ghost - k - 1]) by {
                // For any k in the entire range, if k < mid, it's already covered by the first assertion.
                // If k >= mid, then length - k - 1 < mid, which is also covered by the first assertion.
                // This shows that the reversed property holds for all k.
                x_suffices! {
                    forall|k: int| 0 <= k < length_ghost ==> {
                        if k < mid {
                            have h: v[k] == old(v)[length_ghost - k - 1] by <; assumption;
                        } else {
                            let j = length_ghost - k - 1;
                            have h: j < mid by <; assumption;
                            have h2: v[j] == old(v)[length_ghost - j - 1] by <; h;
                            have h3: v[j] == old(v)[length_ghost - j - 1] ==> v[k] == old(v)[length_ghost - k - 1] by <; h2; 
                        }
                    }
                }
            };
        }
    }
}


//         assert(forall|k: int| 0 <= k < length_ghost ==> 
//                    v[k] == old(v)[length_ghost - k - 1]) by {
//   assertion failed: forall|k: int| 0 <= k < length_ghost ==>                     v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True