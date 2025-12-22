use vstd::prelude::*;

fn main () {}

verus! {

proof fn bitand_with_mask_gives_rounding(x: usize, y: usize)
    requires y != 0, y & sub(y, 1) == 0,
    ensures x & !sub(y, 1) == (x / y) * y,
    decreases y,
{
    if y == 1 {
        assert(x & !sub(1, 1) == x) by(bit_vector);
        assert(x & !sub(y, 1) == (x / y) * y);
    } else {
        assert((y >> 1) < y) by(bit_vector) requires y != 0usize;
        assert((y >> 1) != 0usize) by(bit_vector) requires y != 0usize, y != 1usize;
        assert(y & sub(y, 1) == 0usize ==> (y >> 1) & sub(y >> 1, 1) == 0usize) by(bit_vector)
            requires y != 0usize, y != 1usize;
        bitand_with_mask_gives_rounding(x >> 1, y >> 1);

        assert(
          x & !sub(y, 1) == mul(2, (x >> 1) & !sub(y >> 1, 1))
            && (x >> 1) & !sub(y >> 1, 1) < u64::MAX 
        ) by(bit_vector)
          requires y != 0usize, y != 1usize, y & sub(y, 1) == 0usize;

        let y1 = y >> 1;
        let x1 = x >> 1;
        let b = x % 2;
        assert(y >> 1 == y / 2) by(bit_vector);
        assert(x >> 1 == x / 2) by(bit_vector);
        assert(y == 2 * y1) by {
            assert(y & sub(y, 1) == 0usize ==> y % 2usize == 0usize) by(bit_vector)
                requires y != 0usize, y != 1usize;
        }
        assert(x == 2 * x1 + b);
        assert((2 * x1 + b) / (2 * y1) * (2 * y1)
          == 2 * (x1 / y1 * y1)) by
        {
            let t = (2 * x1 + b) / (2 * y1);
            assert(t * (2 * y1)
                == 2 * (t * y1)) by(nonlinear_arith);
            two_mul_with_bit0(x1 as int, y1 as int);
            two_mul_with_bit1(x1 as int, y1 as int);
            assert((2 * x1 + b) / (2 * y1) == x1 / y1); // by(nonlinear_arith)
                //requires b == 0 || b == 1;
        }
        assert(
          x / y * y
            == 2 * (((x >> 1) / (y >> 1)) * (y >> 1))
        );
        //assert(((x >> 1) / (y >> 1)) * (y >> 1) == ((x >> 1) & !sub(y >> 1, 1)));
        //assert(x & !sub(y, 1) == 2 * ((x >> 1) & !sub(y >> 1, 1)));
        //assert(x & !sub(y, 1) == (x / y) * y);
    }
}

	#[verifier::external_body]
proof fn two_mul_with_bit0(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1) / (2 * y1) == x1 / y1
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn two_mul_with_bit1(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1 + 1) / (2 * y1) == x1 / y1
	{
		unimplemented!()
	}

}
