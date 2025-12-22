use vstd::prelude::*;

fn main() {}

verus! {
#[verifier::integer_ring]

pub proof fn mod_trans(a: int, b: int, c: int)
    requires b != 0, c != 0, a % b == 0, b % c == 0,
    ensures a % c == 0
{
}

}
