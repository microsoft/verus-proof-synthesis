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

    a = 2 * a;
    let c: bool = !b;
    let mut idx: usize = v.len();
    while (idx > 0)
    invariant
        10 < a < 20,  // a is within the assumed bound before modification
        20 < a < 40,  // a is within the expected bound after modification
        c == true,  // b is false, so c is true
        forall |k:int| idx <= k < v.len() ==> v[k] == 1 + a,  // v elements up to idx have been updated
        forall |k:int| 0 <= k < idx ==> v[k] == 1,  // v elements after idx haven't changed. This assertion raises counter-example errors. If I remove this assertion the example is proven.
    {
        idx -= 1;
        v.set(idx, v[idx] + a);
    }
    
    proof {  // inline postcondition
        assert(20 < a < 40);
        assert(forall |k:int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}
}
// Score: (2, 0)
// Safe: False