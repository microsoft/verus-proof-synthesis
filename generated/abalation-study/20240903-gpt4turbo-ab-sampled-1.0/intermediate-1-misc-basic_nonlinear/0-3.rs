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
    assert(x <= 0xffff); // assert x's bound
    assert(y <= 0xffff); // assert y's bound
    assert(x as u64 * y as u64 <= 0xffff * 0xffff); // assert product doesn't exceed bounds in u64 math
    assert(0xffff * 0xffff == 0xffff_ffff); // mathematically equivalent to the maximum value of a 32-bit integer
    assert(0xffff_ffff < 0x100000000); // directly proves the goal
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2