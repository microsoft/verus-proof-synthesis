
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
    // No loops in this function, no arrays to add invariants for.
}

} // verus!

// failed this postcondition
//         x * y <= 0x100000000,
// at the end of the function body
// {
//     // No loops in this function, no arrays to add invariants for.
// }
//   at the end of the function body: {     // No loops in this function, no arrays to add invariants for. }
//   failed this postcondition: x * y <= 0x100000000

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1