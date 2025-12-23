
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
    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(x * y <= 0x100000000 - 1)
        by (nonlinear_arith)
            requires
                x <= 0xffff,
                y <= 0xffff,
                {}
        ;
    assert(x * y <= 0x100000000);
}

}


// Score: (2, 0)
// Safe: True