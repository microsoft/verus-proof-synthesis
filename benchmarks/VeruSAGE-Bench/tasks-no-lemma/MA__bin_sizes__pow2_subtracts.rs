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

proof fn pow2_subtracts(e1:nat, e2:nat)
    requires e1 <= e2,
    ensures 
        pow2(e2 as int) / pow2(e1 as int) == pow2((e2 - e1) as int),
{
}

}