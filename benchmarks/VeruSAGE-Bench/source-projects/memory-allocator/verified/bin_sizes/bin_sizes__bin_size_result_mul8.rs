use vstd::prelude::*;
use vstd::{calc};

use vstd::std_specs::bits::u64_leading_zeros;

fn main() {}

verus! {
pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

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

	#[verifier::external_body]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
	{
		unimplemented!()
	}

pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize
    } else if wsize > 524288 {
        BIN_HUGE as int
    } else {
        let w = (wsize - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;
        bin_idx
    }
}

spec fn property_bin(size:int) -> bool
{
    131072 >= size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start + 8,
{
   if size_start >= size_end {
       true
   } else {
          property_bin(size_start)
       && check_bin(size_start + 8, size_end)
   }
}

spec fn id(i:int) -> bool { true }

	#[verifier::external_body]
proof fn result_bin(size_start:int, size_end:int)
    requires size_start % 8 == 0,
    ensures
        check_bin(size_start, size_end) ==>
            (forall |size: int| size_start <= size < size_end && size % 8 == 0 ==>
                 #[trigger] id(size) && property_bin(size)),
    decreases size_end - size_start + 8,
	{
		unimplemented!()
	}

pub proof fn bin_size_result_mul8(size: usize)
    requires
        size % 8 == 0,
        size <= 131072, //  == MEDIUM_OBJ_SIZE_MAX
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
{
    // TODO: Swap these asserts for the assumes below
    
        /*
	assert(check_bin(0, 8192)) by (compute_only);
	assert(check_bin(8192, 16384)) by (compute_only);
	assert(check_bin(16384, 24576)) by (compute_only);
	assert(check_bin(24576, 32768)) by (compute_only);
	assert(check_bin(32768, 40960)) by (compute_only);
	assert(check_bin(40960, 49152)) by (compute_only);
	assert(check_bin(49152, 57344)) by (compute_only);
	assert(check_bin(57344, 65536)) by (compute_only);
	assert(check_bin(65536, 73728)) by (compute_only);
	assert(check_bin(73728, 81920)) by (compute_only);
	assert(check_bin(81920, 90112)) by (compute_only);
	assert(check_bin(90112, 98304)) by (compute_only);
	assert(check_bin(98304, 106496)) by (compute_only);
	assert(check_bin(106496, 114688)) by (compute_only);
	assert(check_bin(114688, 122880)) by (compute_only);
	assert(check_bin(122880, 131080)) by (compute_only);
        */

	assume(check_bin(0, 8192));
	assume(check_bin(8192, 16384));
	assume(check_bin(16384, 24576));
	assume(check_bin(24576, 32768));
	assume(check_bin(32768, 40960));
	assume(check_bin(40960, 49152));
	assume(check_bin(49152, 57344));
	assume(check_bin(57344, 65536));
	assume(check_bin(65536, 73728));
	assume(check_bin(73728, 81920));
	assume(check_bin(81920, 90112));
	assume(check_bin(90112, 98304));
	assume(check_bin(98304, 106496));
	assume(check_bin(106496, 114688));
	assume(check_bin(114688, 122880));
	assume(check_bin(122880, 131080));

	result_bin(0, 8192);
	result_bin(8192, 16384);
	result_bin(16384, 24576);
	result_bin(24576, 32768);
	result_bin(32768, 40960);
	result_bin(40960, 49152);
	result_bin(49152, 57344);
	result_bin(57344, 65536);
	result_bin(65536, 73728);
	result_bin(73728, 81920);
	result_bin(81920, 90112);
	result_bin(90112, 98304);
	result_bin(98304, 106496);
	result_bin(106496, 114688);
	result_bin(114688, 122880);
	result_bin(122880, 131080);

    assert(id(size as int));
}

pub const BIN_HUGE: u64 = 73;

}
