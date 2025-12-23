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
    // Proof by calculation
    let max_x: u64 = 0xffff;
    let max_y: u64 = 0xffff;

    let product = (x as u64) * (y as u64);
    let max_product = max_x * max_y;

    assert(product <= max_product);
    assert(max_product < 0x100000000);
}
}
// Score: (0, 1)
// Safe: True