use vstd::prelude::*;

fn main() {}

verus!{

// File: spec/utils.rs
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires
        0 <= i < len,
        len > 0,
    ensures
        (i % len) == i,
{
}


}
