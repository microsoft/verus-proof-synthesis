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

pub fn align_down(x: usize, y: usize) -> (res: usize)
    requires y != 0,
    ensures
        res == (x as int / y as int) * y,
        res <= x < res + y,
        res % y == 0,
        (res / y * y) == res,
{
    let mask = y - 1;

    if ((y & mask) == 0) { // power of two?
        let res = x & !mask;
        res
    } else {
        let res = (x / y) * y;
        res
    }
}

}
