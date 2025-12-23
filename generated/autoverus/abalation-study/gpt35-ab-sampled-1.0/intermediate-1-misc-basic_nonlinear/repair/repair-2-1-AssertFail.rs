
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    assert(x <= 0x10000); // Added by AI, for assertion fail
    assert(y <= 0x10000); // Added by AI, for assertion fail
    assert(x * y <= 0x100000000); // Added by AI
}

} // verus!


//     assert(x * y <= 0x100000000); // Added by AI
//   assertion failed: x * y <= 0x100000000

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True