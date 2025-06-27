use vstd::prelude::*;
fn main() {}
verus! {

pub fn havoc_inline_post(v: &mut Vec<u32>, a: u32, b: bool)
    requires
        forall|k: int| 0 <= k < old(v).len() ==> old(v)[k] == 0,
        a == 10,
        b == false,
{
    let mut a: u32 = 0;
    assume(10 < a < 20);
    assume(forall|k: int| 0 <= k < v.len() ==> v[k] == 1);
    a = 2 * a;
    let c: bool = !b;
    let mut idx: usize = v.len();
    while (idx > 0)
        invariant
            0 <= idx <= v.len(),
            10 < a < 20,
            20 < 2 * a < 40,
            forall|k: int| 0 <= k < idx ==> v[k] == 1,
            forall|k: int| idx <= k < v.len() ==> v[k] == 1 + 2 * a,
            v.len() < usize::MAX,
            20 < a < 40,
            forall|k: int| idx <= k < v.len() ==> v[k] == 1 + a,
    {
        idx = idx - 1;
        v.set(idx, v[idx] + a);
    }
    proof {
        assert(20 < a < 40);
        assert(forall|k: int| 0 <= k < v.len() ==> v[k] == 1 + a);
        assert(c == true);
    }
}

} // verus!


// Score: (2, 0)
// Safe: True