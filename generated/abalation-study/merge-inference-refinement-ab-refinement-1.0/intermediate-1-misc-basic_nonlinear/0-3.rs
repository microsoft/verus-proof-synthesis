
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
    // Using math properties: 
    // If x <= 0xffff and y <= 0xffff, then the maximum value of x * y is 0xffff * 0xffff

    assert(x <= 0xffff);
    assert(y <= 0xffff);

    let result: u64 = x as u64 * y as u64;

    // 0xffff * 0xffff = 0xfffe0001, which is less than 0x100000000
    assert(result <= 0xffff * 0xffff);
    assert(0xffff * 0xffff < 0x100000000);
    assert(result <= 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1