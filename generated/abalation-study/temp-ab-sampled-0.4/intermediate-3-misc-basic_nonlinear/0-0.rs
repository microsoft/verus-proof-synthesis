
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
    let mut i: u32 = 0;
    let mut sum: u64 = 0;

    while i < y
        invariant
            i <= y,
            sum <= (i as u64) * (x as u64),
            x <= 0xffff,
            y <= 0xffff,
    {
        sum += x as u64;
        i += 1;
    }

    assert(sum <= 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1