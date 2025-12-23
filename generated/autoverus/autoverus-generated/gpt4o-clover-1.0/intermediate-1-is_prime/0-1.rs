use vstd::prelude::*;

fn main() {}
verus! {

spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < candidate,
            2 <= factor <= candidate,
            forall|k: u64| 2 <= k < factor ==> !divides(k as nat, candidate as nat),
    {
        if candidate % factor == 0 {
            return false;
        }
        factor = factor + 1;
    }
    true
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1