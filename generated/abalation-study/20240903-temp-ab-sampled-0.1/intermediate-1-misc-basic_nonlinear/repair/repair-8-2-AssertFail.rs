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
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64); // Fixed by AI
    assert(0xffff as u64 * 0xffff as u64 == 0xfffe0001); // Corrected by AI
    assert(0xfffe0001 <= 0x100000000); // Corrected by AI
    assert(x as u64 * y as u64 <= 0x100000000);
}

} // verus!

//     assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64); // Fixed by AI
//   assertion failed: x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True