

//from Verus tutorial

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
    // Prove that x and y are within the specified bounds.
    have h1: x <= 0xffff := by assumption;
    have h2: y <= 0xffff := by assumption;

    // Calculate the maximum possible product.
    have h3: x * y <= 0xffff * 0xffff := by
        nlinarith; -- Use nonlinear arithmetic to verify the inequality
    have h4: 0xffff * 0xffff == 0x100000000 - 131072 + 1 := by
        norm_num; -- Normalize the expression to verify the numeric equivalence
    have h5: 0x100000000 - 131072 + 1 == 0x100000000 := by
        norm_num; -- Normalize the expression to verify the numeric equivalence
    have h6: x * y <= 0x100000000 := by
        nlinarith; -- Use nonlinear arithmetic to verify the final inequality

    // Conclude the proof using the established facts.
    done;
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1