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
    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(0xffff * 0xffff <= 0x100000000);
    assert(x * y <= 0xffff * 0xffff);
    assert(x * y <= 0x100000000);
}

} // verus!

// Score: (0, 1)
// Safe: True