
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
    // Loop invariants are generally not required for simple proofs,
    // but ensuring the constraints are restated might still be good practice.
    // Given the nature of the assertion, simple axiomatic proof may suffice.
    // However, for educational purposes, we'll show a structured proof.

    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(0xffff * 0xffff <= 0x100000000);
    // Since x and y are less than or equal to 0xffff, their product will also be less than or equal to this bound
    // Hence assert(x * y <= 0xffff * 0xffff);
    assert(x * y <= 0xffff * 0xffff);
    assert(x * y <= 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1