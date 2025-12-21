use vstd::prelude::*;


fn main() {}

verus! {

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

proof fn log2(i:u64) -> (e:nat)
    requires i >= 1,
    ensures pow2(e as int) <= i < pow2((e+1) as int),
{
    proof_from_false() // TODO: replace with appropriate return value
}

}
