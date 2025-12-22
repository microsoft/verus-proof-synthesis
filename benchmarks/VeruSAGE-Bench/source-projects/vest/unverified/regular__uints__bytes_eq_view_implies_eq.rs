use vstd::prelude::*;

fn main() {}

verus!{

// File: src/regular/uints.rs
proof fn bytes_eq_view_implies_eq<const N: usize>(a: [u8; N], b: [u8; N])
    ensures
        a@ =~= b@ <==> a == b,
{
}


}
