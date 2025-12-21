use vstd::prelude::*;
fn main() {}
verus! {

pub fn do_vec_u8s_match(e1: &Vec<u8>, e2: &Vec<u8>) -> (eq: bool)
    ensures
        eq == (e1@ == e2@),
{
    if e1.len() != e2.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < e1.len() {
        if e1[i] != e2[i] {
            return false;
        }
        i += 1;
    }
    return true;
}

} // verus!
