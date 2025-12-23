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
    let mut i = 0;
    let mut prod = 0;

    while i <= x
        invariant
            i <= x,
            prod == i * y,
            x <= 0xffff,
            y <= 0xffff,
            prod <= 0x100000000,
    {
        i = i + 1;
        prod = i * y;
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1