

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
    let ghost current_max_index: usize = 0;
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            xlen == x.len(),
            1 <= i <= xlen,
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
            max_value == x[( current_max_index ) as int],
    {
        if x[i] > max_value {
            max_value = x[i];
            current_max_index = i;
        }
        i = i + 1;
    }
    assert(exists|i: int| 0 <= i < x.len() && max_value == x[i]);
    max_value
}

} // verus!


// failed this postcondition
//         exists|i: int| 0 <= i < x.len() && res == x[i],
// at the end of the function body
// {
//     assert(x.len() >= 1);
//     let mut max_value = x[0];
//     let mut i: usize = 1;
// ...
//     max_value
// }
//   at the end of the function body: {     assert(x.len() >= 1);     let mut max_value = x[0];     let mut i: usize = 1;     let xlen: usize = x.len();     while (i < xlen)         invariant             xlen == x.len(),             1 <= i <= xlen,             forall|k: int| 0 <= k < i as int ==> max_value >= x[k],     {         if x[i] > max_value {             max_value = x[i];         }         i = i + 1;     }     max_value }
//   failed this postcondition: exists|i: int| 0 <= i < x.len() && res == x[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False