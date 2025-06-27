use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    while (idx < 10)
        invariant
            idx <= 10,
            res == 5 + idx,
            idx < 10 ==> (5 < res),
    {
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    while (idx < 10)
        invariant
            idx <= 10,
            res == 15 + idx,
            idx < 10 ==> (15 < res),
    {
        res = res + 1;
        idx = idx + 1;
    }
    assert(res == 25);
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2