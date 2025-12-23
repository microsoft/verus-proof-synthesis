use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    let mut i: u32 = 0;

    while (i <= x) 
        invariant 
            i <= x,
            y <= 0xffff,
            x <= 0xffff,
            x*y <= 0x100000000,
    {
        i = ( i + 1 ) as u32;
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1