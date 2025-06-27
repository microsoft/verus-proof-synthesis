
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
    // Proof of the given constraint:
    // Since x and y are both <= 0xffff, the maximum value for x*y is:
    // 0xffff * 0xffff = 0xfffe0001 which is less than or equal to 0x100000000.
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1