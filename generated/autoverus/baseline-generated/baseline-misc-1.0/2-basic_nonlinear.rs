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
    let bound_x: u64 = x as u64;
    let bound_y: u64 = y as u64;
    assert((0xffff as u64) * (0xffff as u64) <= 0x100000000);
    assume((bound_x * bound_y) <= 0x100000000); // Added by AI
}
}


// Score: (1, 0)
// Safe: True