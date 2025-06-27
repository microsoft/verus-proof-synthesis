
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
    //mathematically bound that multiplying x*y <= (2^16-1)*(2^16-1) = (2^16)^2 = 2^32
    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(x * y <= 0xffff * 0xffff);
    assert(0xffff * 0xffff == (1 << 16) - 1);
    assert((1 << 16) - 1 <= 1 << 32);
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1