use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{ if i == 0 { 64 } else { u64_leading_zeros(i / 2) - 1 } }


proof fn leading_zeros_between_powers_of_2(i: u64, exp: nat)
    requires
        pow2(exp as int) <= i < pow2((exp + 1) as int),
        1 <= exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
{
    
}

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

}
