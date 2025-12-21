use vstd::prelude::*;


fn main() {}

verus! {

pub proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
}

}