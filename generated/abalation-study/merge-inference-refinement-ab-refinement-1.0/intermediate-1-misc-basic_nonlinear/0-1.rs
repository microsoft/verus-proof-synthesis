
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
    // invariant: the maximum value for x and y are 0xffff (65535)
    // and 0xffff * 0xffff = 0xfffe0001 (4294836225) which is 
    // less than 0x100000000 (4294967296).
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1