
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
    assert(x * y <= 0x100000000); // Added by AI
}

} // verus!


// failed this postcondition
//         x * y <= 0x100000000,
// at the end of the function body
// {
//     // The array x is not modified in this loop because there are no x.set() operations.
// }
//   at the end of the function body: {     // The array x is not modified in this loop because there are no x.set() operations. }
//   failed this postcondition: x * y <= 0x100000000

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True