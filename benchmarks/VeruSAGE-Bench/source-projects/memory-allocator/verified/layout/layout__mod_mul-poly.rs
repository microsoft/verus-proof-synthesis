use vstd::prelude::*;

fn main() {}

verus! {
#[verifier::integer_ring]

pub proof fn mod_mul(a: int, b: int, c: int)
    requires b % c == 0, c != 0
    ensures (a * b) % c == 0,
{
}

}
