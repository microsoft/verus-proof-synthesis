use vstd::prelude::*;

fn main() {}

verus! {

proof fn two_mul_with_bit1(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1 + 1) / (2 * y1) == x1 / y1
{
    assert(
        (2 * x1 + 1) / (2 * y1) == ((2 * x1 + 1) / 2) / y1) by(nonlinear_arith)
        requires y1 != 0;
    assert((2 * x1 + 1) / 2 == x1);
}

}
