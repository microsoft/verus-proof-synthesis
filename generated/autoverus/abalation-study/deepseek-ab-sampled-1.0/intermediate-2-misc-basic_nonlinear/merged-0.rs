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
    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(x * y <= 0xffff * 0xffff);
    assert(0xffff * 0xffff == 0x100000000 - 1);
    assert(x * y <= 0x100000000);
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2