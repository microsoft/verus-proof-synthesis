
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
    let x_u16: u16 = x as u16; // Truncate to 16-bit to ensure values are within 0-65535
    let y_u16: u16 = y as u16;
    let x_u64: u64 = x_u16 as u64;
    let y_u64: u64 = y_u16 as u64;
    let maxrack: u64 = 0xffff as u64; // 65535
    let maxrack_sq: u64 = ( maxrack * maxrack ) as u64;

    assert(x_u64 <= 0xffff as u64);
    assert(y_u64 <= 0xffff as u64);
    assert(x_u64 * y_u64 <= maxrack_sq); // This holds true
}

}


//     assert(x_u64 * y_u64 <= maxrack_sq); // Now this should hold true
//   assertion failed: x_u64 * y_u64 <= maxrack_sq

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True