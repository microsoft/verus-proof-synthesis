use vstd::prelude::*;

fn main() {}

verus! {

proof fn log2(i:u64) -> (e:nat)
    requires i >= 1,
    ensures pow2(e as int) <= i < pow2((e+1) as int),
    decreases i,
{
    if i == 1 {
        0
    } else {
        log2(i / 2) + 1
    }
}

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

}
