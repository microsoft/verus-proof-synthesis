
use vstd::prelude::*;
fn main() {}
verus! {

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    // The array x is not modified in this loop because there are no x.set() operations.
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1