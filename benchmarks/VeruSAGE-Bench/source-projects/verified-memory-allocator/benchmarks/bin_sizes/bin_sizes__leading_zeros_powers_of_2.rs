use vstd::prelude::*;
use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {

	#[verifier::external_body]
proof fn pow2_properties()
    ensures
        forall |e:int| pow2(e) > 0,
        forall |e:int| e > 0 ==> #[trigger] pow2(e) / 2 == pow2(e - 1),
        forall |e1, e2| 0 <= e1 < e2 ==> pow2(e1) < pow2(e2),
        forall |e1, e2| 0 <= e1 && 0 <= e2 ==> pow2(e1) * pow2(e2) == #[trigger] pow2(e1 + e2),
        forall |e1, e2| 0 <= e1 <= e2 ==> pow2(e2) / pow2(e1) == #[trigger] pow2(e2 - e1),
	{
		unimplemented!()
	}

proof fn leading_zeros_powers_of_2(i: u64, exp: nat)
    requires
        i == pow2(exp as int),
        exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases i,
{
    assert(pow2(0) == 1);
    reveal(u64_leading_zeros);
    if exp == 0 {
        assert(u64_leading_zeros(1) == 63) by (compute_only);
    } else {
        assert(pow2(exp as int) > pow2(0)) by { pow2_properties(); }
        assert(i / 2 == pow2(exp as int) / 2 == pow2(exp as int - 1)) by { pow2_properties(); }
        assert(pow2(exp as int - 1) < pow2(exp as int)) by { pow2_properties(); }
        leading_zeros_powers_of_2(i / 2, (exp - 1) as nat);
        assert(u64_leading_zeros(i / 2) == 64 - (exp - 1) - 1);
        assert(u64_leading_zeros(i) == 
               (u64_leading_zeros(i / 2) - 1) as u32 ==
               (64 - (exp - 1) - 1 - 1) as u32 ==
               (64 - exp - 1) as u32
              );
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
