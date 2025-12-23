use vstd::prelude::*;
use vstd::{calc};

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
        
proof fn pow2_properties()
    ensures
        forall |e:int| pow2(e) > 0,
        forall |e:int| e > 0 ==> #[trigger] pow2(e) / 2 == pow2(e - 1),
        forall |e1, e2| 0 <= e1 < e2 ==> pow2(e1) < pow2(e2),
        forall |e1, e2| 0 <= e1 && 0 <= e2 ==> pow2(e1) * pow2(e2) == #[trigger] pow2(e1 + e2),
        forall |e1, e2| 0 <= e1 <= e2 ==> pow2(e2) / pow2(e1) == #[trigger] pow2(e2 - e1),
{

    assert forall |e:int| pow2(e) > 0 by { pow2_positive(e); }
    assert forall |e:int| e > 0 implies #[trigger] pow2(e) / 2 == pow2(e - 1) by {
        assert(pow2(1) == 2) by (compute_only);
        pow2_subtracts(1, e as nat);
    }
    assert forall |e1, e2| 0 <= e1 < e2 implies pow2(e1) < pow2(e2) by {
        let diff = e2 - e1;
        assert(pow2(diff) > 1);
        pow2_positive(diff);
        pow2_positive(e1);
        pow2_positive(e2);
        assert(pow2(e1) * pow2(diff) == pow2(e2)) by { pow2_adds(e1 as nat, diff as nat); }
        mul_ordering(pow2(e1), pow2(diff), pow2(e2));
    }
    assert forall |e1, e2| 0 <= e1 && 0 <= e2 implies pow2(e1) * pow2(e2) == #[trigger] pow2(e1 + e2) by {
        pow2_adds(e1 as nat, e2 as nat);
    }
    assert forall |e1, e2| 0 <= e1 <= e2 implies pow2(e2) / pow2(e1) == #[trigger] pow2(e2 - e1) by {
        pow2_subtracts(e1 as nat, e2 as nat);
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

global size_of usize == 8;

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

pub const BIN_HUGE: u64 = 73;

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

#[verifier::opaque]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if 1 <= bin_idx <= 8 {
       (usize::BITS / 8) as nat * (bin_idx as nat)
    } else if bin_idx == BIN_HUGE {
        // the "real" upper bound on this bucket is infinite
        // the lemmas on bin sizes assume each bin has a lower bound and upper bound
        // so we pretend this is the upper bound

        8 * (524288 + 1)
        //8 * (MEDIUM_OBJ_WSIZE_MAX as nat + 1)
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;

        ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat
    }
}

pub proof fn size_of_bin_mult_word_size(bin_idx: int)
    requires valid_bin_idx(bin_idx),
    ensures size_of_bin(bin_idx) % 8 == 0
{
    reveal(size_of_bin);
    if 1 <= bin_idx <= 8 {
        assert(size_of_bin(bin_idx) == (usize::BITS / 8) as nat * (bin_idx as nat));
        assert(size_of_bin(bin_idx) == 8 * (bin_idx as nat));
        assert(size_of_bin(bin_idx) == 8 * bin_idx);
        assert((8 * bin_idx) % 8 == 0) by (nonlinear_arith);
    } else if bin_idx == BIN_HUGE {
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;
        assert(size_of_bin(bin_idx) == ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat);
        assert(size_of_bin(bin_idx) == (8 * (inner + 5) * pow2(group + 1)) as nat);
        assert(size_of_bin(bin_idx) == 8 * (inner + 5) * pow2(group + 1));
        let sum = (inner + 5);
        let product = sum * pow2(group + 1);
        assert({
            let s = inner + 5;
            let p = s * pow2(group + 1);
            8 * (inner + 5) * pow2(group + 1) == 8 * p
        }) by (nonlinear_arith);
        assert(size_of_bin(bin_idx) == 8 * product);
        mod8(8 * product, product);
    }
}

}
