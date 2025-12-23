use vstd::prelude::*;


fn main () {}

verus! {

	#[verifier::external_body]
proof fn bitand_with_mask_gives_rounding(x: usize, y: usize)
    requires y != 0, y & sub(y, 1) == 0,
    ensures x & !sub(y, 1) == (x / y) * y,
    decreases y,
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn mul_mod_right(a: int, b: int)
    requires b != 0,
    ensures (a * b) % b == 0,
	{
		unimplemented!()
	}

#[inline]
pub fn align_down(x: usize, y: usize) -> (res: usize)
    requires y != 0,
    ensures
        res == (x as int / y as int) * y,
        res <= x < res + y,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        assert(0 <= (x / y) * y <= x) by(nonlinear_arith)
            requires y > 0, x >= 0;

        //assert((y & mask) == 0usize ==> (x & !mask) == sub(x, x % y)) by(bit_vector)
        //    requires mask == sub(y, 1), y >= 1usize;
        if y & mask == 0usize {
            bitand_with_mask_gives_rounding(x, y);
            assert((x & !mask) == (x / y) * y);
            assert((x & !mask) == (x as int / y as int) * y);
        }

        assert((x as int / y as int) == (x / y) as int);

        assert(x / y * y + x % y == x) by(nonlinear_arith) requires y != 0;
        assert(0 <= x % y < y);
        let t = x / y;
        mul_mod_right(t as int, y as int);
        assert(y != 0 ==> (t * y) / y as int * y == t * y) by(nonlinear_arith);
    }

    if ((y & mask) == 0) { // power of two?
        x & !mask
    } else {
        (x / y) * y
    }
}

}
