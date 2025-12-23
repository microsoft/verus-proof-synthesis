use vstd::prelude::*;
fn main() {}

verus! {
    pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires 
        old(y).len() == 0,
    ensures 
        forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
    {
        let mut i: usize = 0;
        let xlen = x.len();
        
        proof {
            // Proving initial invariant
            assert(forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]));
        }
        
        while (i < xlen) 
            invariant 
                0 <= i <= xlen,
                x@.len() == xlen,  // always specify the length of vectors used in the loop
                forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]) // Ensure y contains valid elements
        { 
            if (x[i] % 3 == 0) {
                y.push(x[i]);
                proof {
                    // Prove that the new element added to y meets the condition
                    let new_idx = y.len() - 1;
                    assert(y[new_idx] % 3 == 0);
                    assert(x@.contains(y@[new_idx]));
                }
            }
            i = i + 1;
        }
        
        proof {
            // Final assertion to ensure the postcondition holds
            assert(forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]));
        }
    }
}

// Score: (2, 0)
// Safe: True