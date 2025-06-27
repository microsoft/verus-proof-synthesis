
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
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64) by (nonlinear_arith)
        requires
            x <= 0xffff,
            y <= 0xffff,
            0xffff as u64 * 0xffff as u64 == 0xfffffffe0001 as u64, // Fixed by AI
            {};
    assert(x as u64 * y as u64 <= 0xffffffff as u64);
}

} // verus!


//             0xffff as u64 * 0xffff as u64 == 0xffffffff as u64,
//   None: 0xffff as u64 * 0xffff as u64 == 0xffffffff as u64

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True