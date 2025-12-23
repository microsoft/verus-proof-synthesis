
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
    let x_u64: u64 = x as u64;
    let y_u64: u64 = y as u64;
    // Normalize the numbers to ensure they are within bounds
    assert(arithmetic::normalize(x) <= 0xffff as u32);
    assert(arithmetic::normalize(y) <= 0xffff as u32);
    
    // Use arithmetic fact to ensure multiplication doesn't exceed the limit
    assert(x_u64 * y_u64 <= 0x100000000 as u64);
}

} // verus!


//     assert(x_u64 * y_u64 <= 0x100000000 as u64);
//   assertion failed: x_u64 * y_u64 <= 0x100000000 as u64

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True