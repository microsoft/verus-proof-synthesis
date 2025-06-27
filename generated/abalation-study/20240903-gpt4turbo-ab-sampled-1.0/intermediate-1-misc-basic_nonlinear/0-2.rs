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
    reveal_with_fuel(arith, 10);
    assert(x * y <= 0xffff * 0xffff); // Use specified bounds to prove assertion
    assert(0xffff * 0xffff < 0x100000000); // Show multiplication result is less than the maximum value
    assert(x*y <= 0x100000000); // This is logically implied by the previous steps
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1