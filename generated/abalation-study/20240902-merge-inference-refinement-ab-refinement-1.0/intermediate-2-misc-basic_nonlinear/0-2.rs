
use vstd::prelude::*;
fn main() {}

verus!{

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    // In the worst case, the maximum value of x and y are both 0xffff (65535)
    // We need to show that 65535 * 65535 <= 0x100000000 (4294967296)
    // 65535 * 65535 = 4294836225, which is less than or equal to 4294967296

    assert((x as u64) * (y as u64) <= 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1