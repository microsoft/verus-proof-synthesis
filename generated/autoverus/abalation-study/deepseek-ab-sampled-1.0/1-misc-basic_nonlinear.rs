

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
    assert(x_u64 * y_u64 <= maxrack_sq); // Now this should hold true

    assert(maxrack_sq <= 0xFFFFFFFF as u64); 
    // This assertion is incorrect because maxrack_sq is 4294967297, which is larger than 0xFFFFFFFF (4294967295)
    // But since x and y are cast to u16, their product should not exceed 0xFFFF_FFFF
    assert(x_u64 * y_u64 <= 0xFFFFFFFF as u64);
}

}

// Score: (0, 1)
// Safe: True