
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
      }
    }


// Score: (1, 0)
// Safe: True