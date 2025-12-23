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

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
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

	#[verifier::external_body]
pub proof fn lemma_bin_sizes_constants()
    ensures
        size_of_bin(1) == 8, size_of_bin(1) / 8 == 1,
        size_of_bin(2) == 16, size_of_bin(2) / 8 == 2,
        size_of_bin(3) == 24, size_of_bin(3) / 8 == 3,
        size_of_bin(4) == 32, size_of_bin(4) / 8 == 4,
        size_of_bin(5) == 40, size_of_bin(5) / 8 == 5,
        size_of_bin(6) == 48, size_of_bin(6) / 8 == 6,
        size_of_bin(7) == 56, size_of_bin(7) / 8 == 7,
        size_of_bin(8) == 64, size_of_bin(8) / 8 == 8,
        size_of_bin(9) == 80, size_of_bin(9) / 8 == 10,
        size_of_bin(10) == 96, size_of_bin(10) / 8 == 12,
        size_of_bin(11) == 112, size_of_bin(11) / 8 == 14,
        size_of_bin(12) == 128, size_of_bin(12) / 8 == 16,
        size_of_bin(13) == 160, size_of_bin(13) / 8 == 20,
        size_of_bin(14) == 192, size_of_bin(14) / 8 == 24,
        size_of_bin(15) == 224, size_of_bin(15) / 8 == 28,
        size_of_bin(16) == 256, size_of_bin(16) / 8 == 32,
        size_of_bin(17) == 320, size_of_bin(17) / 8 == 40,
        size_of_bin(18) == 384, size_of_bin(18) / 8 == 48,
        size_of_bin(19) == 448, size_of_bin(19) / 8 == 56,
        size_of_bin(20) == 512, size_of_bin(20) / 8 == 64,
        size_of_bin(21) == 640, size_of_bin(21) / 8 == 80,
        size_of_bin(22) == 768, size_of_bin(22) / 8 == 96,
        size_of_bin(23) == 896, size_of_bin(23) / 8 == 112,
        size_of_bin(24) == 1024, size_of_bin(24) / 8 == 128,
        size_of_bin(25) == 1280, size_of_bin(25) / 8 == 160,
        size_of_bin(26) == 1536, size_of_bin(26) / 8 == 192,
        size_of_bin(27) == 1792, size_of_bin(27) / 8 == 224,
        size_of_bin(28) == 2048, size_of_bin(28) / 8 == 256,
        size_of_bin(29) == 2560, size_of_bin(29) / 8 == 320,
        size_of_bin(30) == 3072, size_of_bin(30) / 8 == 384,
        size_of_bin(31) == 3584, size_of_bin(31) / 8 == 448,
        size_of_bin(32) == 4096, size_of_bin(32) / 8 == 512,
        size_of_bin(33) == 5120, size_of_bin(33) / 8 == 640,
        size_of_bin(34) == 6144, size_of_bin(34) / 8 == 768,
        size_of_bin(35) == 7168, size_of_bin(35) / 8 == 896,
        size_of_bin(36) == 8192, size_of_bin(36) / 8 == 1024,
        size_of_bin(37) == 10240, size_of_bin(37) / 8 == 1280,
        size_of_bin(38) == 12288, size_of_bin(38) / 8 == 1536,
        size_of_bin(39) == 14336, size_of_bin(39) / 8 == 1792,
        size_of_bin(40) == 16384, size_of_bin(40) / 8 == 2048,
        size_of_bin(41) == 20480, size_of_bin(41) / 8 == 2560,
        size_of_bin(42) == 24576, size_of_bin(42) / 8 == 3072,
        size_of_bin(43) == 28672, size_of_bin(43) / 8 == 3584,
        size_of_bin(44) == 32768, size_of_bin(44) / 8 == 4096,
        size_of_bin(45) == 40960, size_of_bin(45) / 8 == 5120,
        size_of_bin(46) == 49152, size_of_bin(46) / 8 == 6144,
        size_of_bin(47) == 57344, size_of_bin(47) / 8 == 7168,
        size_of_bin(48) == 65536, size_of_bin(48) / 8 == 8192,
        size_of_bin(49) == 81920, size_of_bin(49) / 8 == 10240,
        size_of_bin(50) == 98304, size_of_bin(50) / 8 == 12288,
        size_of_bin(51) == 114688, size_of_bin(51) / 8 == 14336,
        size_of_bin(52) == 131072, size_of_bin(52) / 8 == 16384,
        size_of_bin(53) == 163840, size_of_bin(53) / 8 == 20480,
        size_of_bin(54) == 196608, size_of_bin(54) / 8 == 24576,
        size_of_bin(55) == 229376, size_of_bin(55) / 8 == 28672,
        size_of_bin(56) == 262144, size_of_bin(56) / 8 == 32768,
        size_of_bin(57) == 327680, size_of_bin(57) / 8 == 40960,
        size_of_bin(58) == 393216, size_of_bin(58) / 8 == 49152,
        size_of_bin(59) == 458752, size_of_bin(59) / 8 == 57344,
        size_of_bin(60) == 524288, size_of_bin(60) / 8 == 65536,
        size_of_bin(61) == 655360, size_of_bin(61) / 8 == 81920,
        size_of_bin(62) == 786432, size_of_bin(62) / 8 == 98304,
        size_of_bin(63) == 917504, size_of_bin(63) / 8 == 114688,
        size_of_bin(64) == 1048576, size_of_bin(64) / 8 == 131072,
        size_of_bin(65) == 1310720, size_of_bin(65) / 8 == 163840,
        size_of_bin(66) == 1572864, size_of_bin(66) / 8 == 196608,
        size_of_bin(67) == 1835008, size_of_bin(67) / 8 == 229376,
        size_of_bin(68) == 2097152, size_of_bin(68) / 8 == 262144,
        size_of_bin(69) == 2621440, size_of_bin(69) / 8 == 327680,
        size_of_bin(70) == 3145728, size_of_bin(70) / 8 == 393216,
        size_of_bin(71) == 3670016, size_of_bin(71) / 8 == 458752,
        size_of_bin(72) == 4194304, size_of_bin(72) / 8 == 524288,
        size_of_bin(73) == 4194312, size_of_bin(73) / 8 == 524289,
	{
		unimplemented!()
	}

pub proof fn size_le_8_implies_idx_eq_1(bin_idx: int)
    requires valid_bin_idx(bin_idx), size_of_bin(bin_idx) / 8 <= 1,
    ensures bin_idx == 1,
{
    lemma_bin_sizes_constants();
}

pub const BIN_HUGE: u64 = 73;

}
