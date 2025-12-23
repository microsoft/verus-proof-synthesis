
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
            1 <= i <= xlen,
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
    {
        let a: u64 = x[i];
        if a > max_value {
            max_value = a;
            // Introduce a ghost variable to track the index where max_value was updated
            let ghost updated_index: usize = i;
        }
        i = i + 1;
    }
    proof {
        // Use choose to select an index where max_value occurs
        let k: usize = 0;
        if max_value == x[0] {
            assert(k == 0 && x[( k ) as int] == max_value);
            assert(0 <= k && k < x.len());
        } else {
            // Find the index where max_value was updated
            let ghost selected_index: usize = 0;
            for i in 1..xlen {
                if x[( i ) as int] == max_value {
                    let selected_index: usize = i;
                    break;
                }
            }
            let selected_index: usize = selected_index;
            assert(x[( selected_index ) as int] == max_value);
            assert(0 <= selected_index && selected_index < xlen);
        }
        assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
    }
    max_value
}
}





//         assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
//   assertion failed: exists|i: int| 0 <= i < x.len() as int && max_value == x[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False