use vstd::prelude::*;


fn main() {}

verus! {

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

    if ((y & mask) == 0) { // power of two?
        let res = (x + mask) & !mask;
        res
    } else {
        let res = ((x + mask) / y) * y;
        res
    }
}

}
