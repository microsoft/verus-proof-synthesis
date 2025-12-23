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
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64);
    assert(0xffff as u64 * 0xffff as u64 == 0xfffe0001); // Added by AI, for assertion fail
    assert(x as u64 * y as u64 <= 0xffff_ffff);
}

} // verus!
// Score: (0, 1)
// Safe: True