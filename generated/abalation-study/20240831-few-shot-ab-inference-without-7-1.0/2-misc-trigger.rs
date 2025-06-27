
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

spec fn f(seq: Seq<u64>, i: int) -> bool {
    seq[i] == i + 2
}

fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
    requires
        arr.len() > 0,
        0 < i < arr@.len(),
        forall|i: int| f(arr@, i),
    ensures
        ret == i + 2,
        ret == arr@[i as int],
{
    arr[i]
}

} // verus!
// Score: (0, 1)
// Safe: True