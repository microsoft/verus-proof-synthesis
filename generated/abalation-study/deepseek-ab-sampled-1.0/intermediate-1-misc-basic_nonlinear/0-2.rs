
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
    // Establish the upper bounds for x and y
    assert!(x <= 0xFFFF);
    assert!(y <= 0xFFFF);

    // Calculate the maximum possible product of x and y
    let max_product = 0xFFFF * 0xFFFF;
    assert!(max_product == ( 0xFFFE0001 ) as nat);

    // Show that max_product is less than 0x100000000
    assert!(max_product <= ( 0x100000000 ) as nat);

    // Since x and y are within the 16-bit range, their product must be <= 0x100000000
    assert!(x * y <= 0x100000000);
}
}



// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2