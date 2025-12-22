use vstd::prelude::*;

fn main() {}

verus!{

// File: src/utils.rs
/// Helper function to initialize a vector of `u8` with zeros.
pub exec fn init_vec_u8(n: usize) -> (res: Vec<u8>)
    ensures
        res@.len() == n,
{
    let mut i: usize = 0;
    let mut ret: Vec<u8> = Vec::new();
    while i < n
    {
        ret.push(0);
        i = i + 1
    }
    ret
}

}
