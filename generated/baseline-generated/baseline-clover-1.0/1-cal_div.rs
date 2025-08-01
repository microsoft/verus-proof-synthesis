use vstd::prelude::*;

verus! {

fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    let mut x: u32 = 0;
    let mut y: u32 = 191;
    let initial_y: u32 = 191;
    
    while 7 <= y
        invariant
            x <= initial_y / 7,
            y == initial_y - 7 * x,
    {
        x = x + 1;
        y = initial_y - 7 * x;
    }
    
    (x, y)
}

} // verus!
fn main() {}
// Score: (2, 0)
// Safe: False