extern crate verus_builtin_macros as builtin_macros;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;
fn main() {}
verus! {

#[verifier::opaque]
pub open spec fn ckeyhashmap_max_serialized_size() -> usize {
    0x100000
}

pub fn ckeyhashmap_max_serialized_size_exec() -> (r: usize)
    ensures
        r == ckeyhashmap_max_serialized_size(),
{
    0x100000
}

} // verus!
