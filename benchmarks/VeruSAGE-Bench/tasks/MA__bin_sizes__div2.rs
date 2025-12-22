use vstd::prelude::*;


fn main() {}

verus! {

proof fn div2(x: u64, y:int)
    requires y > 0,
    ensures x as int / (y * 2) == (x as int / y) / 2,
{
}

}