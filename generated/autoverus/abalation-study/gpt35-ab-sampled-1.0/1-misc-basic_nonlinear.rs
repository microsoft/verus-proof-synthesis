
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x as u64 * y as u64 <= 0xffff * 0xffff as u64, // Updated assertion based on AI recommendation
{
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64); // Updated assertion based on AI recommendation
}

} // verus!

// Score: (0, 1)
// Safe: True