
use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_16_bit_mul_bound(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000 as u32,
{
    // Split the product into 16-bit parts
    let high_x: u32 = (x >> 16) << 16;
    let low_x: u32 = x & 0xffff;
    let high_y: u32 = (y >> 16) << 16;
    let low_y: u32 = y & 0xffff;
    
    // Since x and y are <= 0xffff, high_x and high_y are 0
    assert(high_x == 0 && high_y == 0);
    
    // Thus, x*y is the product of low_x and low_y
    assert(x * y == low_x * low_y);
    
    // Since both low_x and low_y are <= 0xffff, their product is <= 0x100000000
    assert(low_x * low_y <= 0x100000000 as u32);
}

fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    proof {
        lemma_16_bit_mul_bound(x, y);
    }
}

}


//     assert(x_u64 * y_u64 <= 0x100000000 as u64);
//   assertion failed: x_u64 * y_u64 <= 0x100000000 as u64

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3
// Safe: True