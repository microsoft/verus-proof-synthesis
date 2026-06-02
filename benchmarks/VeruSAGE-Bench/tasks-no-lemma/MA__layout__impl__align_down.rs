use vstd::prelude::*;


fn main () {}

verus! {

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
