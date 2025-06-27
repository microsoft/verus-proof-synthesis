
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
      {
        assert(x * y <= 0x100000000); // Added by AI
      }
    }


// failed this postcondition
//         x * y <= 0x100000000,
// at the end of the function body
//     {
//         // No loops in the function
//     }
//   at the end of the function body: {         // No loops in the function     }
//   failed this postcondition: x * y <= 0x100000000

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True