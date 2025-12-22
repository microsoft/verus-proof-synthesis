use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {

proof fn leading_zeros_between_powers_of_2(i: u64, exp: nat)
    requires
        pow2(exp as int) <= i < pow2((exp + 1) as int),
        1 <= exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases exp,
{
    reveal(u64_leading_zeros);
    if exp == 1 {
        assert(pow2(1) == 2 && pow2(2) == 4) by (compute_only);
        assert(2 <= i < 4);
        assert(u64_leading_zeros(2) == 64 - 1 - 1) by (compute_only);
        assert(u64_leading_zeros(3) == 64 - 1 - 1) by (compute_only);
    } else {
        assert(i / 2 < pow2(exp as int));
        assert(pow2((exp - 1) as int) <= i / 2);
        leading_zeros_between_powers_of_2(i / 2, (exp - 1) as nat);
    }
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
