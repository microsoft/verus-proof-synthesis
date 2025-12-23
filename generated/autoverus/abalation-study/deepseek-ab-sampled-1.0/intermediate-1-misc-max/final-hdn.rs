

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun1(x: &Vec<u64>) -> (res: u64)
    requires
        x.len() >= 1,
    ensures
        forall|i: int| 0 <= i < x.len() ==> res >= x[i],
        exists|i: int| 0 <= i < x.len() && res == x[i],
{
    assert(x.len() >= 1);
    let mut max_value = x[0];
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            xlen == x.len(),
            1 <= i <= xlen, // Changed to 1 <= i <= xlen to satisfy the invariant
            exists|k: int| 0 <= k < i as int ==> max_value == x[k as int],
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k as int],
    {
        if x[i] > max_value {
            max_value = x[i];
        }
        i = i + 1;
        proof {
            let k = if max_value == x[( i ) as int] { i as int } else { 0 };
        }
    }
    max_value
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1