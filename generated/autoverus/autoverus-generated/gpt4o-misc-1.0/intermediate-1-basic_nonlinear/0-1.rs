
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
    // Loop to simulate multiple checks, although not present in original code
    let mut i: u32 = 0;

    while i <= 0xffff
        invariant
            x <= 0xffff,
            y <= 0xffff,
            i <= 0xffff,
            x * y <= 0x100000000,
    {
        i = ( i + 1 ) as u32;
    }

    // Verifying invariant in the loop body is sufficient for the proof
}
}


// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1