

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun1(x: &Vec<u64>) -> (res: u64)
    requires
        x.len() >= 1,
    ensures
        forall|i: int| 0 <= i < x.len() as int ==> res >= x[i],
        exists|i: int| 0 <= i < x.len() as int && res == x[i],
{
    assert(x.len() >= 1);
    let mut max_value = x[0];
    let mut i: usize = 1;
    let xlen: usize = x.len();
    let mut found_index: Option<usize> = None;
    
    while (i < xlen)
        invariant
            xlen == x.len(),
            1 <= i <= xlen,
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
            Option::is_some(( found_index ) as &Option<_>) || (i <= xlen),
    {
        if x[i] > max_value {
            max_value = x[i];
            found_index = Some(i);
            proof {
                assert(max_value == x[i]);
            }
        }
        else if x[i] == max_value {
            found_index = Some(i);
            proof {
                assert(max_value == x[i]);
            }
        }
        i = i + 1;
    }
    proof {
        let i = found_index.unwrap_or(0);
        assert(0 <= i < xlen);
        assert(max_value == x[i]);
        assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
    }
    max_value
}

}


//         assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
//   assertion failed: exists|i: int| 0 <= i < x.len() as int && max_value == x[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False