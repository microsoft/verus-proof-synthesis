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
    assert((x as u64) * (y as u64) <= 0xffff * 0xffff);
    assert((x as u64) * (y as u64) <= 0x100000000);
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1