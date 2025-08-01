
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
    // Since x <= 0xffff and y <= 0xffff, their maximum product is (0xffff * 0xffff)
    // which is 0xfffe0001, and this is less than or equal to 0x100000000.
    // Unwrapping the multiplication for proof.
    proof_assert!(x * y <= 0xffff * 0xffff);
    proof_assert!(0xffff * 0xffff == 0xfffe0001);
    proof_assert!(0xfffe0001 < 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3