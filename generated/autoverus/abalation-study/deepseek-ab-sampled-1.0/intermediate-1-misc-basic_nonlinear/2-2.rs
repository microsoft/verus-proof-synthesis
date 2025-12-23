

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
     have h1: x <= 0xffff, from x <= 0xffff;
     have h2: y <= 0xffff, from y <= 0xffff;
     calc {
         x * y <= 0xffff * 0xffff;
         // 0xffff * 0xffff = 0x100000000
         _ == 0x100000000;
     }
 }
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1