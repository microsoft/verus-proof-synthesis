use vstd::prelude::*;
use vstd::{calc};

use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {
proof fn mod8(x:int, y:int) by (nonlinear_arith)
    requires x == 8 * y,
    ensures  x % 8 == 0,
{}

proof fn div2(x: u64, y:int) by (nonlinear_arith)
    requires y > 0,
    ensures x as int / (y * 2) == (x as int / y) / 2,
{}

proof fn lemma_div_is_ordered(x: int, y: int, z: int) by (nonlinear_arith)
    requires 
        x <= y,
        0 < z,
    ensures x / z <= y / z
{}

pub proof fn lemma_div_by_multiple(b: int, d: int) by (nonlinear_arith)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{}

proof fn mul_assoc(x: nat, y: nat, z: nat) by (nonlinear_arith)
    ensures (x * y) * z == y * (x * z)
{}

proof fn mul_ordering(x: nat, y: nat, z: nat) by (nonlinear_arith)
    requires
        0 < x && 1 < y && 0 < z,
        x * y == z,
    ensures
        x < z,
{}

proof fn pow2_positive(e:int)
    ensures pow2(e) > 0,
    decreases e,
{
    if e <= 0 {
    } else {
        pow2_positive(e - 1);
    }
}

proof fn pow2_adds(e1:nat, e2:nat)
    ensures 
        pow2(e1 as int) * pow2(e2 as int) == pow2((e1 + e2) as int),
    decreases e1,        
{
    if e1 == 0 {
        assert(pow2(e1 as int) == 1);
    } else {
        calc! { (==)
            pow2(e1 as int) * pow2(e2 as int); {}
            (pow2((e1 as int - 1) as int) * 2) * pow2(e2 as int);
                { mul_assoc(pow2((e1 as int - 1) as int), 2, pow2(e2 as int)); }
            2 * (pow2((e1 as int - 1) as int) * pow2(e2 as int));
                { pow2_adds((e1 as int - 1) as nat, e2); }
            2 * pow2((e1 - 1 + e2) as int); {}
            pow2((e1 + e2) as int);
        }
    }
}

proof fn pow2_subtracts(e1:nat, e2:nat)
    requires e1 <= e2,
    ensures 
        pow2(e2 as int) / pow2(e1 as int) == pow2((e2 - e1) as int),
{
    calc! { (==)
        pow2(e2 as int) / pow2(e1 as int);
            { pow2_adds((e2 - e1) as nat, e1); }
        pow2((e2 - e1) as int) * pow2(e1 as int) / pow2(e1 as int);
            { 
                pow2_positive(e1 as int);
                lemma_div_by_multiple(pow2((e2 - e1) as int) as int, pow2(e1 as int) as int); 
            }
        pow2((e2 - e1) as int);
    }    
}
        
proof fn shift_is_div(x:u64, shift:u64)
    requires 0 <= shift < 64,
    ensures x >> shift == x as nat / pow2(shift as int),
    decreases shift,
{
    if shift == 0 {
        assert(x >> 0 == x) by (bit_vector);
        assert(pow2(0) == 1) by (compute_only);
    } else {
        assert(x >> shift == (x >> ((sub(shift, 1)) as u64)) / 2) by (bit_vector)
            requires 0 < shift < 64;

        assert(x as nat / pow2(shift as int) == (x as nat / (pow2((shift - 1) as int) * pow2(1)))) by {
            pow2_adds((shift - 1) as nat, 1);
        }
        assert(x as nat / pow2(shift as int) == (x as nat / pow2((shift - 1) as int)) / 2) by {
            pow2_positive((shift - 1) as int);
            div2(x, pow2((shift - 1) as int) as int);
        }

        calc!{ (==)
            (x >> shift) as nat; 
                {}
            ((x >> ((sub(shift, 1)) as u64)) / 2) as nat;
                { shift_is_div(x, (shift - 1) as u64); }
            (x as nat / pow2(shift - 1 as int)) / 2;
                {}
            x as nat / pow2(shift as int);
        }
    }
}

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
