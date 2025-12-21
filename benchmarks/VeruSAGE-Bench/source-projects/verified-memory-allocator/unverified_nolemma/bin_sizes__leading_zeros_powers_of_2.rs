use vstd::prelude::*;

use vstd::std_specs::bits::u64_leading_zeros;
fn main() {}

verus! {

/*
Definitions from vstd
-----
vstd::std_specs::bits
-----
#[verifier::opaque]
pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{
    if i == 0 {
        64
    } else {
        u64_leading_zeros(i / 2) - 1
    }
}
-----
*/

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

proof fn leading_zeros_powers_of_2(i: u64, exp: nat)
    requires
        i == pow2(exp as int),
        exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
{
}

}
