use vstd::prelude::*;


fn main() {}

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
pub fn align_up(x: usize, y: usize) -> (res: usize)
    requires y != 0,
        x + y - 1 <= usize::MAX,
    ensures
        res == ((x + y - 1) / y as int) * y,
        x <= res <= x + y - 1,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    proof {
        if y & mask == 0 {
            bitand_with_mask_gives_rounding((x + y - 1) as usize, y);
            assert(((x + mask) as usize) & !mask == ((x + y - 1) / y as int) * y);
        }

        let z = x + mask;
        assert(z / y as int * y + z % y as int == z) by(nonlinear_arith) requires y != 0;

        let t = (x + y - 1) / y as int;
        mul_mod_right(t, y as int);
        assert(y != 0 ==> (t * y) / y as int * y == t * y) by(nonlinear_arith);
    }

    if ((y & mask) == 0) { // power of two?
        (x + mask) & !mask
    } else {
        ((x + mask) / y) * y
    }
}

}
