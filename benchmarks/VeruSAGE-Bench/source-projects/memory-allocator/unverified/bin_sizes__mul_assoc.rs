use vstd::prelude::*;


fn main() {}

verus! {

proof fn mul_assoc(x: nat, y: nat, z: nat)
    ensures (x * y) * z == y * (x * z)
{
}

}