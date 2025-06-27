
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
    // No loops in this function, no arrays to add invariants for.
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1