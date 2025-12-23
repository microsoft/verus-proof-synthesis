use vstd::prelude::*;
fn main() {}

verus!{
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    assert(x <= 0xffff);  //max value for x
    assert(y <= 0xffff);  //max value for y
    // Since 0xffff * 0xffff = 0xfffe0001, which is less than 0x100000000
    assert(x * y <= 0x100000000); // proving the postcondition
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1