use vstd::prelude::*;


fn main() {}

verus! {

proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires 
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
}

}