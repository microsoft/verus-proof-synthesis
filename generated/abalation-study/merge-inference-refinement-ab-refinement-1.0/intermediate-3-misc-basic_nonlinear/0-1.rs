
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
    // We use a simple multiplication overflow rule for unsigned integers
    // The maximum value for a 16-bit unsigned integer is 0xffff (65535)
    // When multiplying two maximum 16-bit values, the result is:
    // 65535 * 65535 = 4294836225, which is less than or equal to 0xffffffff (32-bit max)
    // But we need to prove x * y ≤ 0x100000000 (one more than the max value for 32-bit)
    // 0xffff * 0xffff = 0xfffe0001
    // which is less than 0x100000000.
    // Since we're dealing with unsigned 32-bit integers, no overflow occurs for this calculation.
    
    // Proof logic (in comments)
    // Since 0xffff is equivalent to 2^16 - 1, let's calculate the square:
    // (2^16 - 1) * (2^16 - 1) = 2^32 - 2^16 - 2^16 + 1 = 2^32 - 2*(2^16) + 1 = 0x100000000 - 0x20000 + 1
    // Clearly, 0x100000000 - 0x20000 + 1 is less than 0x100000000.
    
    // Just asserting for automatic verification
    assert(x * y <= 0x100000000);
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1