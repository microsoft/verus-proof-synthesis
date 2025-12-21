use vstd::prelude::*;


fn main() {}

verus! {

proof fn mul_ordering(x: nat, y: nat, z: nat)
    requires
        0 < x && 1 < y && 0 < z,
        x * y == z,
    ensures
        x < z,
{
}

}