
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
    proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
    {
        proof {
            assert(x * y <= 0x100000000); // Added by AI
        }
    }
} // verus!


// failed this postcondition
//         x * y <= 0x100000000,
// at the end of the function body
//     {
//         // No loops in the function
//     }
//   at the end of the function body: {         // No loops in the function     }
//   failed this postcondition: x * y <= 0x100000000

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True