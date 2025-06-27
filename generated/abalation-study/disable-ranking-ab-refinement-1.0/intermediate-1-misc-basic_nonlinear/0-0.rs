use vstd::prelude::*;
fn main() {}

verus!{

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    while (a <= x)
        invariant
            a <= x + 1,
            y <= 0xffff,
    {
        while (b <= y)
            invariant
                b <= y + 1,
                (a * b) <= 0x100000000,
        {
            if a * b > 0x100000000 {
                assert(false);
            }
            b = ( b + 1 ) as u32;
        }
        a = ( a + 1 ) as u32;
    }
}
}


// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1