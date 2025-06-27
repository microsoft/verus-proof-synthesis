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
    let mut i: u32 = 0;
    let mut j: u32 = 0;

    while i <= x
        invariant
            i <= x,
            y <= 0xffff,
            i * y <= 0x100000000,
    {
        while j <= y
            invariant
                i <= x,
                j <= y,
                x <= 0xffff,
                y <= 0xffff,
                i * j <= 0x100000000,
        {
            j += 1;
        }
        i += 1;
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1