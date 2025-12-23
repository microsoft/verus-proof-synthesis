
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000 as u32,
{
    #[verifier(atomic)]
    proof fn x_le(x: u32, x_hex: u32) {
        assert(x <= x_hex);
    }

    #[verifier(atomic)]
    proof fn y_le(y: u32, y_hex: u32) {
        assert(y <= y_hex);
    }

    #[verifier(atomic)]
    proof fn product_le(x: u32, y: u32, product_max: u32) {
        assert(x * y <= product_max);
    }

    x_le(x, 0xffff);
    y_le(y, 0xffff);
    product_le(x, y, 0x100000000);
}

}


//     assert(x_u64 * y_u64 <= 0x100000000 as u64);
//   assertion failed: x_u64 * y_u64 <= 0x100000000 as u64

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False