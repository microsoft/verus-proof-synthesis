use vstd::prelude::*;

fn main() {}

verus!{

// File: userspace.rs
pub const FLAG_INITIALIZED: u8 = 0x01;

pub fn recycle_flags_decide(current_flags: u8) -> (result: u8)
    ensures
        result == (current_flags | FLAG_INITIALIZED),
        (result & FLAG_INITIALIZED) == FLAG_INITIALIZED,
{
    let result = current_flags | FLAG_INITIALIZED;
    let flag_initialized = FLAG_INITIALIZED;

    assert((result & flag_initialized) == flag_initialized) by (bit_vector)
        requires result == (current_flags | flag_initialized);
    result
}


}
