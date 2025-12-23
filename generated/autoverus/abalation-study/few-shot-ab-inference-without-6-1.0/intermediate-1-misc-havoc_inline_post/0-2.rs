use vstd::prelude::*;
fn main() {}
verus!{
pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires 
        forall |k:int| 0 <= k < old(v).len() ==> old(v)[k] == 0,
        a == 10,
        b == false,
{  
    let mut a: u32 = 0;

    // Variables a and v are havocked. Their values are randomly reset, but their new values follow the following assumptions.
    assume(10 < a < 20);
    assume(forall |k:int| 0 <= k < v.len() ==> v[k] == 1);

    a = 2*a;
    let c: bool = !b;
    let mut idx: usize = v.len();
    
    while (idx > 0)
        invariant
            idx <= v.len(),
            10 < (a / 2) < 20,  // since a was assumed to be between 10 and 20 before doubling
            20 < a < 40,
            forall |k:int| 0 <= k < v.len() ==> v[k] == 1 || (idx <= k < v.len() ==> v[k] == 1 + a),
            c == true,
    {
        idx = idx - 1;
        v.set(idx, v[idx] + a);
    }
    
    proof {  // inline postcondition
        assert(20 < a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2