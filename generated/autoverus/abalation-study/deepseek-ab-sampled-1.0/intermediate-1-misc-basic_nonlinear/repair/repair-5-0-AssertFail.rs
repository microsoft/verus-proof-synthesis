

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
     let x_u64: u64 = x as u64;
     let y_u64: u64 = y as u64;
     assert(x_u64 * y_u64 <= 0xFFFFFFFF as u64);
 }
}

//     assert(x_u64 * y_u64 <= 0xFFFFFFFF as u64);
//   assertion failed: x_u64 * y_u64 <= 0xFFFFFFFF as u64

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True