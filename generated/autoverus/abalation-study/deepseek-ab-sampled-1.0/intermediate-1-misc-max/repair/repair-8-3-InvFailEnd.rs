
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
    let mut k: usize = 0;
    while (i < xlen)
        invariant
            xlen == x.len(),
            1 <= i <= xlen,
            exists|k: usize| 0 <= k < i ==> max_value == x[( k ) as int],
            forall|k: usize| 0 <= k < i ==> max_value >= x[( k ) as int],
        decreases
            xlen - i
    {
        if x[i] > max_value {
            max_value = x[i];
            k = i;
        }
        i = i + 1;
        proof {
            assert(exists|k: usize| 0 <= k < i ==> max_value == x[( k ) as int]);
        }
    }
    max_value
}
}





//             exists|k: int| 0 <= k < i as int ==> max_value == x[k],
//   None: exists|k: int| 0 <= k < i as int ==> max_value == x[k]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False