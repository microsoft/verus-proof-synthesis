use vstd::prelude::*;

verus! {

fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    let mut x: u32 = 0;
    let mut y: u32 = 191;

    while 7 <= y
        invariant
            x <= 27,
            y < 191,
            y == 191 - 7 * x,
    {
        x = x + 1;
        y = 191 - 7 * x;
    }

    (x, y)
}

} // verus!
fn main() {}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1